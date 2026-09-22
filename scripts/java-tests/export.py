#!/usr/bin/env python3
"""Export query traces from the pinned Java test suite. Requires a built Java checkout."""
import pathlib, re, shutil, subprocess, sys
root = pathlib.Path(__file__).resolve().parents[2]
java = pathlib.Path(sys.argv[1]).resolve()
out = root / 'target/java-export'
src = out / 'src'
classes = out / 'classes'
shutil.copytree(java / 'src/test/java', src, dirs_exist_ok=True)
classes.mkdir(parents=True, exist_ok=True)
base = src / 'org/semanticweb/HermiT/reasoner/AbstractReasonerTest.java'
s = base.read_text().replace('new Reasoner(configuration,m_ontology,descriptionGraphs)', 'ExportReasoner.create(configuration,m_ontology,descriptionGraphs)')
s = s.replace('m_reasoner=(Reasoner)factory.createReasoner(m_ontology,c);', 'm_reasoner=ExportReasoner.create(c,m_ontology,Collections.<DescriptionGraph>emptySet());')
s = s.replace('new EntailmentChecker(m_reasoner,m_dataFactory).entails(', 'm_reasoner.isEntailed(')
base.write_text(s)
for path in (src / 'org/semanticweb/HermiT/reasoner').glob('*.java'):
    s = path.read_text()
    s = s.replace('new ReasonerFactory()', 'new ExportReasoner.Factory()').replace('new Reasoner.ReasonerFactory()', 'new ExportReasoner.Factory()')
    s = re.sub(r'new EntailmentChecker\(m_reasoner,\s*m_dataFactory\)\.entails\(', 'm_reasoner.isEntailed(', s)
    if path.stem in ['AnyURITest','RDFPlainLiteralTest']:
        for method in ['createValueSpaceSubset','conjoinWithDRNegation','conjoinWithDR','parseLiteral']:
            s=s.replace('DatatypeRegistry.'+method+'(', 'ExportDatatypes.'+method+'(')
    s=s.replace('new RDFPlainLiteralLengthInterval(', 'new ExportDatatypes.StringInterval(').replace('new BinaryDataLengthInterval(', 'new ExportDatatypes.BinaryInterval(').replace('new DateTimeInterval(', 'new ExportDatatypes.DateInterval(')
    if path.stem=='DateTimeTest':s=s.replace('DateTime.parse(', 'ExportDatatypes.parseDateTime(')
    if path.stem=='BinaryDataTest':s=s.replace('BinaryData.parseBase64Binary(', 'ExportDatatypes.parseBase64Binary(')
    path.write_text(s)
# Structural tests retain their original expected strings, including tests that
# Java's aggregate suite disables because fresh-definition ordering can differ.
structural = src / 'org/semanticweb/HermiT/structural'
p = structural / 'AbstractStructuralTest.java'
t = p.read_text().replace('        return actualStrings;', '        org.semanticweb.HermiT.reasoner.ExportReasoner.structural("clausify",m_ontology,actualStrings);\n        return actualStrings;')
t = t.replace('protected static void assertContainsAll(String testName,Collection<String> actual,String[] control) {', 'protected static void assertContainsAll(String testName,Collection<String> actual,String[] control) {\n        org.semanticweb.HermiT.reasoner.ExportReasoner.structuralExpected(control);')
p.write_text(t)
p = structural / 'NormalizationTest.java'
t = p.read_text().replace('        assertContainsAll(normalizedAxiomsString,expectedAxiomsString);', '        org.semanticweb.HermiT.reasoner.ExportReasoner.structural("normalize",m_ontology,java.util.Arrays.asList(expectedAxiomsString));\n        assertContainsAll(normalizedAxiomsString,expectedAxiomsString);')
p.write_text(t)
source = (java / 'src/main/java/org/semanticweb/HermiT/Reasoner.java').read_text()
names = set('isConsistent isEntailed isSatisfiable hasType hasObjectPropertyRelationship getInstances getSuperClasses getSubClasses getEquivalentClasses getDisjointClasses getSubObjectProperties getSuperObjectProperties getObjectPropertyInstances getObjectPropertyValues getDisjointObjectProperties getSubDataProperties getSuperDataProperties getDataPropertyValues getTypes getObjectPropertyDomains getObjectPropertyRanges getDataPropertyDomains getInverseObjectProperties getSameIndividuals getDifferentIndividuals getEquivalentObjectProperties getEquivalentDataProperties isSameIndividual hasDataPropertyRelationship canProcessPendingChangesIncrementally'.split())
methods = []
for match in re.finditer(r'    public (.+?) (\w+)\(([^\n]*)\) (?:throws [^{]+)?\{', source):
    ret, name, params = match.groups()
    if name not in names: continue
    # Commas inside generic type arguments do not separate parameters.
    pieces = re.split(r',(?=[^>]*(?:<|$))', params) if params else []
    args = ','.join(p.strip().split()[-1] for p in pieces)
    methods.append(f'''    @Override public {ret} {name}({params}) {{
        depth++;
        try {{
            {ret} result=super.{name}({args});
            if (depth==1 && ready) record("{name}",new Object[]{{{args}}},result);
            return result;
        }} catch (RuntimeException ex) {{
            if (depth==1 && ready) recordException("{name}",new Object[]{{{args}}},ex);
            throw ex;
        }} finally {{ depth--; }}
    }}''')
skeleton = (root / 'scripts/java-tests/ExportReasoner.java').read_text()
(src / 'org/semanticweb/HermiT/reasoner/ExportReasoner.java').write_text(skeleton.replace('// GENERATED OVERRIDES', '\n'.join(methods)))
for name in ['ExportTests.java','ExportDatatypes.java']:
    shutil.copy(root / 'scripts/java-tests' / name, src / 'org/semanticweb/HermiT/reasoner' / name)
cp = str(java / 'target/classes') + ':' + (java / 'classpath.txt').read_text().strip()
subprocess.run(['javac','-J-Xmx256m','-nowarn','-cp',cp,'-d',str(classes),*[str(p) for p in src.rglob('*.java')]],check=True)
cp = ':'.join([str(classes), str(java/'src/test/resources'), cp])
(root/'target/java-export/classpath.txt').write_text(cp)
if len(sys.argv)>2:
    subprocess.run(['java','--add-opens=java.base/java.lang=ALL-UNNAMED','-Xmx256m','-cp',cp,'org.semanticweb.HermiT.reasoner.ExportTests',*sys.argv[2:]],check=True)
