package org.semanticweb.HermiT.reasoner;
import java.util.*;
import java.lang.reflect.*;
import java.nio.file.*;
import junit.framework.*;
public class ExportTests {
    public static void main(String[] args) throws Exception {
        ExportReasoner.destination=Paths.get(args[0]); Files.createDirectories(ExportReasoner.destination.resolve("cases"));
        for(int i=1;i<args.length;i++) {
            String[] selection=args[i].split("#",2);
            Class<?> cls=Class.forName("org.semanticweb.HermiT."+selection[0]);
            TreeSet<String> methods=new TreeSet<>();
            for(Method m:cls.getMethods()) if(m.getName().startsWith("test") && m.getParameterCount()==0 && m.getReturnType()==void.class) methods.add(m.getName());
            for(String method:methods) {
                if(selection.length==2 && !method.equals(selection[1]))continue;
                String name=selection[0]+"."+method;
                System.out.println("RUN "+name); System.out.flush();
                ExportReasoner.operations=new ArrayList<>(); ExportReasoner.nextID=0;
                TestCase test=(TestCase)cls.getConstructor(String.class).newInstance(method);
                TestResult result=new TestResult(); test.run(result);
                Map<String,Object> row=new TreeMap<>(); row.put("java",name); row.put("operations",ExportReasoner.operations);
                List<String> errors=new ArrayList<>();
                for(Enumeration<TestFailure> e=result.errors();e.hasMoreElements();) errors.add(e.nextElement().trace());
                for(Enumeration<TestFailure> e=result.failures();e.hasMoreElements();) errors.add(e.nextElement().trace());
                row.put("java_errors",errors);
                ExportReasoner.JSON.writerWithDefaultPrettyPrinter().writeValue(ExportReasoner.destination.resolve("cases").resolve(name+".json").toFile(),row);
                System.out.println("DONE "+name+" operations="+ExportReasoner.operations.size()+" errors="+errors.size());
            }
        }
    }
}
