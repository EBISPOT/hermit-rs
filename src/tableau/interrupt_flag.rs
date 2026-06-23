// Port of org.semanticweb.HermiT.tableau.InterruptFlag.
//
// Signals that the current reasoning task should be interrupted, either by an
// explicit `interrupt()` (from another thread) or by exceeding the per-task
// timeout. HermiT drives the timeout from a background timer thread that sets
// the flag; since the engine calls `check_interrupt` very frequently, this port
// equivalently checks the elapsed time at each `check_interrupt`, avoiding the
// timer thread while preserving the observable throwing behaviour.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use crate::time::Instant;
use std::time::Duration;

/// The reason a task was interrupted (mirrors the OWL-API exceptions thrown by
/// HermiT's `checkInterrupt`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InterruptError {
    Interrupted,
    Timeout,
}

pub struct InterruptFlag {
    timeout: Option<Duration>,
    interrupted: Arc<AtomicBool>,
    task_start: Option<Instant>,
}

impl InterruptFlag {
    pub fn new(individual_task_timeout_millis: i64) -> InterruptFlag {
        let timeout = if individual_task_timeout_millis > 0 {
            Some(Duration::from_millis(individual_task_timeout_millis as u64))
        } else {
            None
        };
        InterruptFlag {
            timeout,
            interrupted: Arc::new(AtomicBool::new(false)),
            task_start: None,
        }
    }

    pub fn check_interrupt(&self) -> Result<(), InterruptError> {
        if self.interrupted.load(Ordering::Acquire) {
            return Err(InterruptError::Interrupted);
        }
        if let (Some(timeout), Some(start)) = (self.timeout, self.task_start) {
            if start.elapsed() >= timeout {
                return Err(InterruptError::Timeout);
            }
        }
        Ok(())
    }

    /// Whether `check_interrupt` could possibly report an interrupt in the near
    /// future, used to skip the per-worker-step poll in the hottest VM loop when
    /// there is provably nothing to detect. True if a timeout is configured (it may
    /// elapse) or the interrupt latch is already set. When this is false the loop
    /// may legitimately defer its poll to the next outer step: an interrupt that
    /// arrives mid-loop is still caught at the next `check_interrupt`, and the
    /// derived facts are unaffected either way (cancellation is best-effort, with
    /// the same latched-`Err` surfaced by `run_calculus`).
    #[inline]
    pub fn poll_can_fire(&self) -> bool {
        self.timeout.is_some() || self.interrupted.load(Ordering::Acquire)
    }

    /// Returns a handle that can be used from another thread to interrupt the
    /// current task.
    pub fn interrupt_handle(&self) -> InterruptHandle {
        InterruptHandle {
            interrupted: self.interrupted.clone(),
        }
    }

    /// Creates a new `InterruptFlag` (no timeout) that shares the same
    /// interrupted-latch as `handle`.  Used by `DatalogEngine` to inject its
    /// own `InterruptHandle` into a freshly-built `Tableau`
    /// (DatalogEngine.java:38,54: `m_interruptFlag` is created once and passed
    /// into every `Tableau` constructor call).
    pub(crate) fn from_handle(handle: &InterruptHandle) -> InterruptFlag {
        InterruptFlag {
            timeout: None,
            interrupted: handle.interrupted.clone(),
            task_start: None,
        }
    }

    pub fn interrupt(&self) {
        self.interrupted.store(true, Ordering::Release);
    }

    pub fn start_task(&mut self) {
        self.interrupted.store(false, Ordering::Release);
        self.task_start = Some(Instant::now());
    }

    pub fn end_task(&mut self) {
        self.task_start = None;
        self.interrupted.store(false, Ordering::Release);
    }

    pub fn dispose(&self) {
        // No background timer thread to dispose of in this port.
    }
}

/// A thread-safe handle for interrupting an `InterruptFlag` from elsewhere.
#[derive(Clone)]
pub struct InterruptHandle {
    interrupted: Arc<AtomicBool>,
}

impl InterruptHandle {
    pub fn interrupt(&self) {
        self.interrupted.store(true, Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_timeout_never_fires() {
        // -1 (HermiT's default) means no timeout: even after a task starts and
        // time passes, check_interrupt stays Ok -- zero behavioural change (F10).
        let mut flag = InterruptFlag::new(-1);
        flag.start_task();
        std::thread::sleep(Duration::from_millis(5));
        assert_eq!(flag.check_interrupt(), Ok(()));
        flag.end_task();
    }

    #[test]
    fn positive_timeout_fires_after_elapsing() {
        let mut flag = InterruptFlag::new(1); // 1ms
        flag.start_task();
        std::thread::sleep(Duration::from_millis(10));
        assert_eq!(flag.check_interrupt(), Err(InterruptError::Timeout));
        flag.end_task();
        // After end_task the flag is reset.
        assert_eq!(flag.check_interrupt(), Ok(()));
    }

    #[test]
    fn explicit_interrupt_via_handle_fires() {
        let mut flag = InterruptFlag::new(-1);
        flag.start_task();
        let handle = flag.interrupt_handle();
        assert_eq!(flag.check_interrupt(), Ok(()));
        handle.interrupt();
        assert_eq!(flag.check_interrupt(), Err(InterruptError::Interrupted));
    }
}
