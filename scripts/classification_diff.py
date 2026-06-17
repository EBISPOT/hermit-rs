#!/usr/bin/env python3
"""Soundness/completeness diff between hermit-rs classification output and a
reference reasoner (e.g. ROBOT/HermiT), comparing TRANSITIVE CLOSURES so that
direct-vs-indirect representation differences do not show up as false diffs.

Usage:
    hermit -c ONT.ofn > rust.txt                         # hermit-rs output
    robot reason --reasoner hermit -i ONT.ofn -o ref.owl  # reference
    robot convert -i ref.owl --format ofn -o ref.ofn
    python3 classification_diff.py rust.txt ref.ofn

Parses OWL functional-syntax SubClassOf/EquivalentClasses (stripping leading
Annotation(...) wrappers and expanding the file's Prefix(...) declarations),
restricts to the shared class vocabulary, and reports:
    SPURIOUS = rust entails, reference does not  (unsoundness)
    MISSING  = reference entails, rust does not  (incompleteness)
"""
import re,collections,itertools,sys
def prefixes(f):
    pm={}
    for line in open(f):
        m=re.match(r"Prefix\(([^:]*):=<([^>]+)>\)",line.strip())
        if m: pm[m.group(1)]=m.group(2)
    return pm
def mkfull(pm):
    def full(tok):
        tok=tok.strip()
        if tok.startswith("<") and tok.endswith(">"): return tok[1:-1]
        if ":" in tok:
            p,l=tok.split(":",1)
            if p in pm: return pm[p]+l
        return tok
    return full
def top_args(inner):
    args=[];d=0;cur=""
    for ch in inner:
        if ch=='(':d+=1;cur+=ch
        elif ch==')':d-=1;cur+=ch
        elif ch==' ' and d==0:
            if cur:args.append(cur);cur=""
        else:cur+=ch
    if cur:args.append(cur)
    return args
def atomic(a): return "(" not in a  # named class token
def load(f,is_rust):
    full=mkfull(prefixes(f)); s=set()
    for line in open(f):
        line=line.strip()
        for kw,k in (("SubClassOf(",8+3),):
            pass
        if line.startswith("SubClassOf("):
            args=[a for a in top_args(line[11:-1]) if not a.startswith("Annotation(")]
            if len(args)==2 and atomic(args[0]) and atomic(args[1]):
                a,b=full(args[0]),full(args[1])
                if a!=b: s.add((a,b))
        elif line.startswith("EquivalentClasses("):
            args=[a for a in top_args(line[18:-1]) if not a.startswith("Annotation(")]
            args=[a for a in args if atomic(a)]
            cl=[full(a) for a in args]
            for a,b in itertools.permutations(cl,2): s.add((a,b))
    return s
def tc(edges):
    succ=collections.defaultdict(set)
    for a,b in edges: succ[a].add(b)
    ch=True
    while ch:
        ch=False
        for a in list(succ):
            new=set()
            for b in list(succ[a]): new|=succ.get(b,set())
            if not new<=succ[a]: succ[a]|=new; ch=True
    return {(a,b) for a in succ for b in succ[a] if a!=b}
rustf,orcf=sys.argv[1],sys.argv[2]
rust=tc(load(rustf,True)); orc=tc(load(orcf,False))
THING="http://www.w3.org/2002/07/owl#Thing"
sh=({a for a,_ in rust}|{b for _,b in rust})&({a for a,_ in orc}|{b for _,b in orc})
f=lambda s:{(a,b) for a,b in s if a in sh and b in sh and b!=THING}
rust=f(rust);orc=f(orc)
extra=rust-orc;miss=orc-rust
print(f"TC rust:{len(rust)} oracle:{len(orc)}  SPURIOUS:{len(extra)}  MISSING:{len(miss)}")
for a,b in sorted(extra)[:12]: print("  SPUR",a.split('/')[-1],"->",b.split('/')[-1])
