"""Translate the straight-line Java NI regression scenarios without dropping assertions."""
import pathlib,re
root=pathlib.Path(__file__).resolve().parents[2]
src=(root/'tests/java/upstream/java/org/semanticweb/HermiT/tableau/NIRuleTest.java').read_text()
src=re.sub(r'//[^\n]*','',src)
def arguments(s):
    depth=0;out=[];start=0;quote=False;escape=False
    for i,ch in enumerate(s):
        if quote:
            if escape:escape=False
            elif ch=='\\':escape=True
            elif ch=='"':quote=False
        elif ch=='"':quote=True
        elif ch in '({[':depth+=1
        elif ch in ')}]':depth-=1
        elif ch==',' and depth==0:out.append(s[start:i].strip());start=i+1
    out.append(s[start:].strip());return out

def replace_calls(s,name,convert):
    while name+'(' in s:
        a=s.index(name+'('); start=a+len(name)+1;depth=1;pos=start;quoted=False
        while depth:
            ch=s[pos]
            if ch=='"' and s[pos-1]!='\\':quoted=not quoted
            if not quoted:
                if ch=='(':depth+=1
                if ch==')':depth-=1
            pos+=1
        s=s[:a]+convert(arguments(s[start:pos-1]))+s[pos:]
    return s

def expression(s):
    s=s.replace('m_tableau.getDependencySetFactory().emptySet()','DependencySet::Permanent(t.dependency_set_factory.empty_set())')
    s=s.replace('m_manager.m_annotatedEqualities.getFirstFreeTupleIndex()','t.annotated_equalities.len()')
    s=s.replace('m_tableau.doIteration()','do_iteration(&mut t,&mut manager,None)')
    for method in ['isActive','isMerged','isPruned']:
        snake=re.sub(r'(?<!^)([A-Z])',r'_\1',method).lower()
        s=re.sub(r'(\w+)\.'+method+r'\(\)',r't.nodes[\1].'+snake+'()',s)
    s=re.sub(r'(\w+)\.getCanonicalNode\(\)',r't.get_canonical_node(\1)',s)
    s=replace_calls(s,'getRootNodeFor',lambda a:'root(&t,'+','.join(a)+')')
    s=replace_calls(s,'m_extensionManager.containsAssertion',lambda a:'contains(&t,'+a[0]+',&['+','.join(a[1:])+'])')
    s=replace_calls(s,'m_extensionManager.getAssertionDependencySet',lambda a:'dependency(&t,'+a[0]+',&['+','.join(a[1:])+'])')
    s=replace_calls(s,'m_tableau.getDependencySetFactory().addBranchingPoint',lambda a:'DependencySet::Permanent(t.dependency_set_factory.add_branching_point(&'+a[0]+','+a[1]+'))')
    return s

out=['// Mechanically ported from java 37ec30ac: tableau.NIRuleTest.\n// Regenerate with scripts/java-tests/port_ni.py.\n#![allow(non_snake_case, unused_mut, unused_variables)]\nuse super::*;\nuse crate::model::*;\nuse crate::tableau::DependencySetOps;\n']
for match in re.finditer(r'public void (test\w+)\(\)\s*\{',src):
    start=match.end();depth=1;end=start
    while depth:
        if src[end]=='{':depth+=1
        if src[end]=='}':depth-=1
        end+=1
    body=src[start:end-1]
    out.append('#[test]\nfn '+match[1]+'() {\n    let (mut t,mut manager)=ni_tableau();\n    let Symbols {A,B,NEG_A,R,S,T,AT_MOST_ONE_R_A,AT_MOST_TWO_R_A,EQ_ONE_R_A,EQ_TWO_R_A,EQ_ONE_S_A}=symbols();\n')
    for raw in body.split(';'):
        line=' '.join(raw.split()).strip()
        if not line:continue
        line=expression(line).replace('Equality.INSTANCE','DLPredicate::Equality')
        line=re.sub(r'^(Node|DependencySet) (\w+)\s*=',r'let mut \2=',line)
        line=replace_calls(line,'m_tableau.createNewNINode',lambda a:'t.create_new_ni_node(&'+a[0]+')')
        line=replace_calls(line,'m_tableau.createNewTreeNode',lambda a:'t.create_new_tree_node(&'+a[0]+','+a[1]+')')
        line=replace_calls(line,'m_extensionManager.addAssertion',lambda a:'add(&mut t,'+a[0]+',&['+','.join(a[1:-2])+'],&'+a[-2]+','+a[-1]+')')
        line=replace_calls(line,'m_extensionManager.addConceptAssertion',lambda a:'add(&mut t,'+a[0]+',&['+a[1]+'],&'+(('DependencySet::Permanent('+a[2]+')') if a[2].startswith('dependency(') else a[2])+','+a[3]+')')
        line=replace_calls(line,'m_manager.addAnnotatedEquality',lambda a:'t.add_annotated_equality(&eq('+a[0]+'),'+','.join(a[1:-1])+',&'+a[-1]+')')
        line=replace_calls(line,'m_extensionManager.setClash',lambda a:'t.set_clash(&'+a[0]+')')
        line=replace_calls(line,'assertDependencySet',lambda a:'assert_dependency('+a[0]+',&['+','.join(a[1:])+'])')
        line=replace_calls(line,'assertUnprocessedDisjunctions',lambda a:'assert_disjunctions(&t,'+a[0]+',&['+','.join(a[1:])+'])')
        line=replace_calls(line,'assertTrue',lambda a:'assert!('+a[0]+')')
        line=replace_calls(line,'assertFalse',lambda a:'assert!(!('+a[0]+'))')
        for method,op in [('assertEquals','assert_eq!'),('assertSame','assert_eq!'),('assertNotSame','assert_ne!')]:line=replace_calls(line,method,lambda a,op=op:op+'('+','.join(a)+')')
        line=replace_calls(line,'assertNull',lambda a:'assert_eq!('+a[0]+',usize::MAX)')
        if '&mut t' in line and 'dependency(&t' in line:
            line=replace_calls(line,'dependency',lambda a:'saved_dependency')
            out.append('    let saved_dependency=dependency(&t,S,&[a_n1,a_n1]);\n')
        out.append('    '+line+';\n')
    out.append('}\n')
(root/'src/reasoner/java_ni_tests.rs').write_text(''.join(out)+'\n'+(root/'scripts/java-tests/ni_helpers.rs').read_text())
import subprocess
subprocess.run(['rustfmt','--edition','2021',str(root/'src/reasoner/java_ni_tests.rs')],check=True)
