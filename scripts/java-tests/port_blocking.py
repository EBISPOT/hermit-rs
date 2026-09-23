"""Translate both original BlockingValidatorTest scenarios, including every assertion."""
import pathlib,re,runpy
root=pathlib.Path(__file__).resolve().parents[2]
helper=runpy.run_path(str(root/'scripts/java-tests/port_ni.py'))
args=helper['arguments'];calls=helper['replace_calls']
# Both upstream scenarios hang their tree nodes directly off NI roots. With the
# inverse roles these ontologies use, ValidatedSingleDirectBlockingChecker only lets a
# tree node block or be blocked when its parent is a tree or graph node, so the
# upstream fixture fails at its first blocking assertion in Java too. Port the
# corrected fixture beside it, which places the old roots under one fresh NI root.
src=(root/'tests/java/corrected/java/org/semanticweb/HermiT/tableau/BlockingValidatorTest.java').read_text()
src=re.sub(r'//[^\n]*','',src)
def pred(p):
 if p.startswith('AnnotatedEquality.create'):
  a=args(p[p.index('(')+1:-1]);return f'DLPredicate::AnnotatedEquality(AnnotatedEquality::create({a[0]},Role::AtomicRole(AtomicRole::create("{a[1]}")),LiteralConcept::AtomicConcept(AtomicConcept::create("{a[2]}"))))'
 return 'predicate("'+p+'")'
def atom(s):
 a=args(s[len('Atom.create('):-1]);return 'atom('+pred(a[0])+',&['+','.join('"'+v+'"' for v in a[1:])+'])'
def atoms(s):
 s=s[s.index('{')+1:s.rindex('}')];return 'vec!['+','.join(atom(a) for a in args(s))+']'
out=['// Direct translation of the corrected Java BlockingValidatorTest\n// (tests/java/corrected/); regenerate with port_blocking.py.\n#![allow(non_snake_case,unused_variables)]\nuse super::java_tableau_tests::*;\nuse super::*;\nuse crate::model::*;\n']
for m in re.finditer(r'public void (test\w+)\(\) \{(.*?)\n    \}',src,re.S):
 out.append('#[test]\nfn '+m[1]+'(){\nif crate::java_test_support::isolated(concat!(module_path!(), "::'+m[1]+'").trim_start_matches("hermit_rs::")) { return; }\nlet mut clauses=indexmap::IndexSet::new();\n')
 body=m[2]
 for raw in body.split(';'):
  line=' '.join(raw.split())
  if not line:continue
  if 'DLClause.create(' in line:
   a=args(line[line.index('DLClause.create(')+len('DLClause.create('):-1]);out.append('clauses.insert(DLClause::create('+','.join(atoms(v) for v in a)+'));\n');continue
  if line=='TEST_DL_ONTOLOGY=getTestDLOntology(dlClauses)':
   out.append('let dl=test_dl(clauses.into_iter().collect());let (mut t,_manager)=tableau(&dl,true);\n');continue
  if line.startswith(('Set<','dlClauses.add','DirectBlockingChecker ','m_blockingStrategy=','ExistentialExpansionStrategy ','m_tableau=','m_extensionManager=')):continue
  line=line.replace('m_tableau.getDependencySetFactory().emptySet()','DependencySet::Permanent(t.dependency_set_factory.empty_set())').replace('m_extensionManager.containsClash()','t.contains_clash()').replace('m_blockingStrategy.computeBlocking(false)','t.compute_blocking()')
  line=re.sub(r'^(DependencySet|Node) (\w+)=',r'let \2=',line)
  line=calls(line,'m_tableau.createNewNINode',lambda a:'t.create_new_ni_node(&'+a[0]+')')
  line=calls(line,'m_tableau.createNewTreeNode',lambda a:'t.create_new_tree_node(&'+a[0]+','+a[1]+')')
  for fn in ['m_extensionManager.addAssertion','m_extensionManager.addConceptAssertion']:
   line=calls(line,fn,lambda a:'add(&mut t,'+pred(a[0])+',&['+','.join(a[1:-2])+'],&'+a[-2]+','+a[-1]+')')
  line=re.sub(r'(\w+)\.isDirectlyBlocked\(\)',r't.nodes[\1].is_directly_blocked()',line)
  line=re.sub(r'(\w+)\.isBlocked\(\)',r't.nodes[\1].is_blocked()',line)
  line=re.sub(r'(\w+)\.getBlocker\(\)==(\w+)',r't.nodes[\1].get_blocker()==Some(\2)',line)
  if line.startswith('BlockingValidator validator='):line='let validator=crate::tableau::blocking_validator::BlockingValidator::new(dl.get_dl_clauses())'
  line=calls(line,'validator.isBlockValid',lambda a:'validator.is_block_valid(&mut t,'+a[0]+')')
  line=calls(line,'assertTrue',lambda a:'assert!('+a[0]+')');line=calls(line,'assertFalse',lambda a:'assert!(!('+a[0]+'))')
  out.append(line+';\n')
 out.append('}\n')
(root/'src/reasoner/java_blocking_tests.rs').write_text(''.join(out))
import subprocess
subprocess.run(['rustfmt','--edition','2021',str(root/'src/reasoner/java_blocking_tests.rs')],check=True)
