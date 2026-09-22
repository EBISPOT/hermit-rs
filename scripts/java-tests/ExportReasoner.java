package org.semanticweb.HermiT.reasoner;

import java.util.*;
import java.io.*;
import java.nio.file.*;
import java.security.MessageDigest;
import org.semanticweb.HermiT.*;
import org.semanticweb.HermiT.model.DescriptionGraph;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.*;
import com.fasterxml.jackson.databind.ObjectMapper;

/** Only top-level calls are recorded; the original JUnit assertions still run. */
public class ExportReasoner extends Reasoner {
    static final ObjectMapper JSON=new ObjectMapper();
    static List<Object> operations=new ArrayList<>();
    static int nextID;
    static Path destination;
    static OWLOntology renderingOntology;
    static {
        try { renderingOntology=org.semanticweb.owlapi.apibinding.OWLManager.createOWLOntologyManager().createOntology(); }
        catch(Exception e) {throw new ExceptionInInitializerError(e);}
    }
    int depth;
    int id;
    boolean ready;
    public static class Factory extends Reasoner.ReasonerFactory {
        @Override protected OWLReasoner createHermiTOWLReasoner(Configuration c,OWLOntology o) {
            return create(c,o,Collections.<DescriptionGraph>emptySet());
        }
    }
    public ExportReasoner(Configuration c,OWLOntology o,Collection<DescriptionGraph> g) {
        super(c,o,g);
        id=nextID++;
        ready=true;
        Map<String,Object> row=new TreeMap<>();
        row.put("op","create"); row.put("id",id); row.put("ontology",saveOntology(o));
        row.put("blocking",c.blockingStrategyType.toString());
        row.put("direct_blocking",c.directBlockingType.toString());
        row.put("cache",c.blockingSignatureCacheType.toString());
        row.put("existential",c.existentialStrategyType.toString());
        row.put("individual_policy",c.individualNodeSetPolicy.toString());
        row.put("throw_inconsistent",c.throwInconsistentOntologyException);
        row.put("ignore_unsupported",c.ignoreUnsupportedDatatypes);
        row.put("buffer_changes",c.bufferChanges);
        row.put("description_graphs",g.size());
        operations.add(row);
    }
    public static Reasoner create(Configuration c,OWLOntology o,Collection<DescriptionGraph> g) {
        try { return new ExportReasoner(c,o,g); }
        catch (RuntimeException ex) {
            Map<String,Object> row=new TreeMap<>(); row.put("op","invalid");
            row.put("ontology",saveOntology(o)); row.put("error",ex.toString()); operations.add(row);
            throw ex;
        }
    }
    public static void structural(String op,OWLOntology ontology,Collection<String> expected) {
        Map<String,Object> row=new TreeMap<>();row.put("op",op);row.put("ontology",saveOntology(ontology));row.put("expected",expected);
        operations.add(row);
    }
    public static void structuralExpected(String[] expected) {
        ((Map<String,Object>)operations.get(operations.size()-1)).put("expected",expected);
    }
    static String saveOntology(OWLOntology o) {
        try {
            TreeSet<String> axioms=new TreeSet<>();
            for (OWLOntology imp:o.getImportsClosure()) for (OWLAxiom a:imp.getAxioms()) axioms.add(render(a));
            StringBuilder s=new StringBuilder("Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\nPrefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\nPrefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(\n");
            for(String a:axioms) s.append(a).append('\n');
            s.append(")\n");
            byte[] bytes=s.toString().getBytes("UTF-8");
            byte[] digest=MessageDigest.getInstance("SHA-256").digest(bytes);
            StringBuilder hash=new StringBuilder(); for(byte b:digest) hash.append(String.format("%02x",b));
            String name=hash.toString()+".ofn";
            Files.createDirectories(destination.resolve("ontologies"));
            Files.write(destination.resolve("ontologies").resolve(name),bytes);
            return name;
        } catch(Exception ex) { throw new RuntimeException(ex); }
    }
    static Object encode(Object o) {
        if(o==null || o instanceof Boolean || o instanceof Number || o instanceof String) return o;
        if(o instanceof NodeSet) return encode(((NodeSet<?>)o).getNodes());
        if(o instanceof Node) return encode(((Node<?>)o).getEntities());
        if(o instanceof Map) {
            Map<String,Object> m=new TreeMap<>();
            for(Map.Entry<?,?> e:((Map<?,?>)o).entrySet()) m.put(encode(e.getKey()).toString(),encode(e.getValue()));
            return m;
        }
        if(o instanceof Collection) {
            List<Object> list=new ArrayList<>(); for(Object v:(Collection<?>)o) list.add(encode(v));
            list.sort(Comparator.comparing(Object::toString)); return list;
        }
        if(o instanceof OWLObject) return render((OWLObject)o);
        return o.toString();
    }
    static String render(OWLObject o) {
        StringWriter writer=new StringWriter();
        org.semanticweb.owlapi.functional.renderer.FunctionalSyntaxObjectRenderer renderer=new org.semanticweb.owlapi.functional.renderer.FunctionalSyntaxObjectRenderer(renderingOntology,writer);
        org.semanticweb.owlapi.util.DefaultPrefixManager prefixes=new org.semanticweb.owlapi.util.DefaultPrefixManager();
        prefixes.clear(); renderer.setPrefixManager(prefixes);
        o.accept(renderer);
        return writer.toString().trim();
    }
    void record(String op,Object[] args,Object result) {
        Map<String,Object> row=new TreeMap<>(); row.put("op",op); row.put("id",id);
        List<Object> a=new ArrayList<>(); for(Object v:args) a.add(encode(v));
        row.put("args",a); row.put("expected",encode(result)); operations.add(row);
        if(op.equals("canProcessPendingChangesIncrementally") || !getConfiguration().bufferChanges) row.put("ontology",saveOntology(getRootOntology()));
    }
    void recordException(String op,Object[] args,RuntimeException ex) {
        record(op,args,null);
        ((Map<String,Object>)operations.get(operations.size()-1)).put("exception",ex.getClass().getName());
    }
    @Override public void printHierarchies(PrintWriter out,boolean classes,boolean objects,boolean data) {
        depth++;
        try {
            StringWriter buffer=new StringWriter(); PrintWriter writer=new PrintWriter(buffer);
            super.printHierarchies(writer,classes,objects,data); writer.flush();
            out.print(buffer.toString());
            if(depth==1 && ready) record("printHierarchies",new Object[]{classes,objects,data},buffer.toString());
        } finally {depth--;}
    }
    @Override public void classifyClasses() {
        depth++;
        try {
            super.classifyClasses();
            if(depth==1 && ready) record("classifyClasses",new Object[]{},null);
        } catch(RuntimeException ex) {
            if(depth==1 && ready) recordException("classifyClasses",new Object[]{},ex);
            throw ex;
        } finally {depth--;}
    }
    @Override public void precomputeInferences(InferenceType... types) {
        depth++;
        try {
            super.precomputeInferences(types);
            if(depth==1 && ready) record("precomputeInferences",new Object[]{Arrays.asList(types)},null);
        } catch(RuntimeException ex) {
            if(depth==1 && ready) recordException("precomputeInferences",new Object[]{Arrays.asList(types)},ex);
            throw ex;
        } finally {depth--;}
    }
    @Override public void flush() {
        if (ready && depth==0) {
            Map<String,Object> row=new TreeMap<>(); row.put("op","flush"); row.put("id",id);
            row.put("ontology",saveOntology(getRootOntology())); operations.add(row);
        }
        depth++; try { super.flush(); } finally {depth--;}
    }
    // GENERATED OVERRIDES
}
