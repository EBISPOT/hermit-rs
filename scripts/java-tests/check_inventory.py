#!/usr/bin/env python3
"""Fail if any pinned Java test is missing, unported, duplicated or assertion-free."""
import json,pathlib,re
root=pathlib.Path(__file__).resolve().parents[2];fixtures=root/'tests/java'
inventory=json.loads((fixtures/'inventory.json').read_text());native=json.loads((fixtures/'native-cases.json').read_text());disabled=json.loads((fixtures/'disabled.json').read_text())
source_methods=set()
for source in (fixtures/'upstream/java').rglob('*.java'):
 text=re.sub(r'/\*.*?\*/|//[^\n]*','',source.read_text(),flags=re.S)
 package=source.parent.name
 for method in re.findall(r'public\s+void\s+(test\w*)\s*\(\s*\)',text):source_methods.add(f'{package}.{source.stem}.{method}')
listed={row['java'] for row in inventory['declared_methods']}
assert len(listed)==len(inventory['declared_methods']), 'duplicate inventory identity'
assert source_methods==listed,(source_methods-listed,listed-source_methods)
for row in inventory['declared_methods']:
 name=row['java'];assert (fixtures/'upstream'/row['source']).is_file()
 if name.startswith('owl_wg_tests.'):assert row['port'].startswith('owl_wg_conformance::');continue
 if name in disabled:assert row['port']=='upstream_disabled';continue
 if name in native:
  assert row['port']==native[name]
  function=native[name].rsplit('::',1)[1]
  assert any(re.search(r'fn\s+'+re.escape(function)+r'\s*\(',p.read_text()) for base in [root/'src',root/'tests'] for p in base.rglob('*.rs')),name
 else:
  p=fixtures/'cases'/(name+'.json');d=json.loads(p.read_text());assert d['java']==name
  assert d['operations'],f'{name}: no assertions captured'
for p in (fixtures/'cases').glob('*.json'):
 d=json.loads(p.read_text());assert d['java']==p.stem
 if p.stem not in native and p.stem not in disabled:assert d['operations'],p
 for op in d['operations']:
  if 'ontology' in op:assert (fixtures/'ontologies'/op['ontology']).is_file(),p
expected=json.loads((fixtures/'expected-failures.json').read_text())
executed={p.stem for p in (fixtures/'cases').glob('*.json') if p.stem not in native and p.stem not in disabled}|set(native.values())
assert set(expected)<=executed, f'stale exception identities: {set(expected)-executed}'
for name,failure in expected.items():
 assert failure['origin'] in {'Rust/Java discrepancy','upstream assertion also fails','resource limit'},name
 assert failure['signature'],name
print(f"{len(listed)} declared Java methods accounted for; {len(native)} native ports; {len(list((fixtures/'cases').glob('*.json')))} replay fixtures (including inherited suites); {len(disabled)} empty upstream overrides.")
