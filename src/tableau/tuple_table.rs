// Port of org.semanticweb.HermiT.tableau.TupleTable.
//
// A growable store of fixed-arity tuples, used by the extension tables. HermiT
// stores `Object[]` tuples in fixed-size pages; this port keeps the same index
// arithmetic over a single flat, growable backing vector (the paging is a
// memory-layout detail with no observable effect). Tuple slots can be nulled,
// so elements are stored as `Option<T>`.

const PAGE_SIZE: usize = 512;

pub struct TupleTable<T> {
    arity: usize,
    objects: Vec<Option<T>>,
    first_free_tuple_index: usize,
}

impl<T> TupleTable<T> {
    pub fn new(arity: usize) -> TupleTable<T> {
        let mut table = TupleTable {
            arity,
            objects: Vec::new(),
            first_free_tuple_index: 0,
        };
        table.clear();
        table
    }

    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn get_first_free_tuple_index(&self) -> usize {
        self.first_free_tuple_index
    }

    fn slot(&self, tuple_index: usize, object_index: usize) -> usize {
        tuple_index * self.arity + object_index
    }

    pub fn get_tuple_object(&self, tuple_index: usize, object_index: usize) -> Option<&T> {
        debug_assert!(object_index < self.arity);
        self.objects[self.slot(tuple_index, object_index)].as_ref()
    }

    pub fn set_tuple_object(&mut self, tuple_index: usize, object_index: usize, object: Option<T>) {
        let slot = self.slot(tuple_index, object_index);
        self.objects[slot] = object;
    }

    pub fn truncate(&mut self, new_first_free_tuple_index: usize) {
        self.first_free_tuple_index = new_first_free_tuple_index;
    }

    pub fn nullify_tuple(&mut self, tuple_index: usize) {
        let start = tuple_index * self.arity;
        for slot in &mut self.objects[start..start + self.arity] {
            *slot = None;
        }
    }

    pub fn clear(&mut self) {
        // One page worth of capacity to start, mirroring HermiT.
        self.objects = (0..self.arity * PAGE_SIZE).map(|_| None).collect();
        self.first_free_tuple_index = 0;
    }
}

impl<T: Clone> TupleTable<T> {
    /// Stores the tuple, returning its index.
    pub fn add_tuple(&mut self, tuple_buffer: &[T]) -> usize {
        let new_tuple_index = self.first_free_tuple_index;
        let capacity = self.objects.len() / self.arity;
        if new_tuple_index == capacity {
            // Grow by a page.
            self.objects
                .extend((0..self.arity * PAGE_SIZE).map(|_| None));
        }
        let start = new_tuple_index * self.arity;
        for (offset, value) in tuple_buffer.iter().enumerate() {
            self.objects[start + offset] = Some(value.clone());
        }
        self.first_free_tuple_index += 1;
        new_tuple_index
    }

    /// Copies the stored tuple at `tuple_index` into a freshly allocated vector.
    pub fn retrieve_tuple(&self, tuple_index: usize) -> Vec<Option<T>> {
        let start = tuple_index * self.arity;
        self.objects[start..start + self.arity].to_vec()
    }
}

impl<T: PartialEq> TupleTable<T> {
    /// Whether the first `compare_length` elements of `tuple_buffer` match the
    /// stored tuple at `tuple_index`.
    pub fn tuple_equals(
        &self,
        tuple_buffer: &[T],
        tuple_index: usize,
        compare_length: usize,
    ) -> bool {
        let start = tuple_index * self.arity;
        for source_index in (0..compare_length).rev() {
            match &self.objects[start + source_index] {
                Some(stored) if *stored == tuple_buffer[source_index] => {}
                _ => return false,
            }
        }
        true
    }

    /// Like `tuple_equals`, but reads from `tuple_buffer` through
    /// `position_indexes` (the projection used by the indexed extension tables).
    pub fn tuple_equals_indexed(
        &self,
        tuple_buffer: &[T],
        position_indexes: &[usize],
        tuple_index: usize,
        compare_length: usize,
    ) -> bool {
        let start = tuple_index * self.arity;
        for source_index in (0..compare_length).rev() {
            match &self.objects[start + source_index] {
                Some(stored) if *stored == tuple_buffer[position_indexes[source_index]] => {}
                _ => return false,
            }
        }
        true
    }
}
