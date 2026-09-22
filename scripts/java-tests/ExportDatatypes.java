package org.semanticweb.HermiT.reasoner;
import java.util.*;
import java.net.URI;
import org.semanticweb.HermiT.datatypes.*;
import org.semanticweb.HermiT.datatypes.binarydata.*;
import org.semanticweb.HermiT.datatypes.datetime.*;
import org.semanticweb.HermiT.datatypes.rdfplainliteral.*;
import org.semanticweb.HermiT.model.Constant;
import org.semanticweb.HermiT.model.DatatypeRestriction;

public class ExportDatatypes {
    static final String XSD="http://www.w3.org/2001/XMLSchema#";
    static Object literal(String lexical,String datatype){Map<String,Object> m=new TreeMap<>();m.put("lexical",lexical);m.put("datatype",datatype);return m;}
    static Object value(Object v) {
        if(v instanceof URI)return literal(v.toString(),XSD+"anyURI");
        if(v instanceof String)return literal(v.toString(),XSD+"string");
        if(v instanceof BinaryData)return literal(v.toString(),XSD+(((BinaryData)v).getBinaryDataType()==BinaryDataType.HEX_BINARY?"hexBinary":"base64Binary"));
        if(v instanceof DateTime){
            DateTime d=(DateTime)v;
            Map<String,Object> m=(Map<String,Object>)literal(v.toString(),XSD+"dateTime");
            m.put("millis",d.getTimeOnTimeline()-719162L*86400000L);
            m.put("has_tz",d.hasTimeZoneOffset());m.put("tz_offset",d.hasTimeZoneOffset()?d.getTimeZoneOffset():0);
            return m;
        }
        if(v instanceof RDFPlainLiteralDataValue){RDFPlainLiteralDataValue d=(RDFPlainLiteralDataValue)v;return literal(d.getString()+"@"+d.getLanguageTag(),"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral");}
        throw new IllegalArgumentException("unhandled datatype value "+v.getClass());
    }
    static Object restriction(DatatypeRestriction dr,boolean negated){
        Map<String,Object> m=new TreeMap<>();m.put("datatype",dr.getDatatypeURI());m.put("negated",negated);
        List<Object> facets=new ArrayList<>();for(int i=0;i<dr.getNumberOfFacetRestrictions();i++)facets.add(Arrays.asList(dr.getFacetURI(i),literal(dr.getFacetValue(i).getLexicalForm(),dr.getFacetValue(i).getDatatypeURI())));
        m.put("facets",facets);return m;
    }
    static List<Object> length(String type,int min,int max){
        DatatypeRestriction dr=DatatypeRestriction.create(XSD+type,new String[]{XSD+"minLength",XSD+"maxLength"},new Constant[]{Constant.create(""+min,XSD+"integer"),Constant.create(""+max,XSD+"integer")});
        return Arrays.asList(restriction(dr,false));
    }
    static void record(String operation,List<Object> ranges,Object argument,Object expected){
        Map<String,Object> m=new TreeMap<>();m.put("op","datatype");m.put("operation",operation);m.put("ranges",ranges);m.put("argument",argument);m.put("expected",expected);ExportReasoner.operations.add(m);
    }
    static class Subset implements ValueSpaceSubset {
        final ValueSpaceSubset delegate;final List<Object> ranges;
        Subset(ValueSpaceSubset d,List<Object> r){delegate=d;ranges=r;}
        public boolean hasCardinalityAtLeast(int n){boolean v=delegate.hasCardinalityAtLeast(n);record("cardinality",ranges,n,v);return v;}
        public boolean containsDataValue(Object o){boolean v=delegate.containsDataValue(o);record("contains",ranges,value(o),v);return v;}
        public void enumerateDataValues(Collection<Object> values){
            try {delegate.enumerateDataValues(values);List<Object> expected=new ArrayList<>();for(Object v:values)expected.add(value(v));record("enumerate",ranges,null,expected);}
            catch(RuntimeException e){record("infinite",ranges,null,true);throw e;}
        }
    }
    public static ValueSpaceSubset createValueSpaceSubset(DatatypeRestriction dr){return new Subset(DatatypeRegistry.createValueSpaceSubset(dr),Arrays.asList(restriction(dr,false)));}
    public static ValueSpaceSubset conjoinWithDRNegation(ValueSpaceSubset s,DatatypeRestriction dr){Subset d=(Subset)s;List<Object> r=new ArrayList<>(d.ranges);r.add(restriction(dr,true));return new Subset(DatatypeRegistry.conjoinWithDRNegation(d.delegate,dr),r);}
    public static ValueSpaceSubset conjoinWithDR(ValueSpaceSubset s,DatatypeRestriction dr){Subset d=(Subset)s;List<Object> r=new ArrayList<>(d.ranges);r.add(restriction(dr,false));return new Subset(DatatypeRegistry.conjoinWithDR(d.delegate,dr),r);}
    public static Object parseLiteral(String lexical,String datatype) throws MalformedLiteralException {
        try {Object v=DatatypeRegistry.parseLiteral(lexical,datatype);record("parse",Collections.emptyList(),literal(lexical,datatype),value(v));return v;}
        catch(MalformedLiteralException e){record("parse",Collections.emptyList(),literal(lexical,datatype),null);throw e;}
    }
    public static class StringInterval extends RDFPlainLiteralLengthInterval {
        final List<Object> ranges;
        public StringInterval(LanguageTagMode mode,int min,int max){super(mode,min,max);if(mode!=LanguageTagMode.ABSENT)throw new AssertionError();ranges=length("string",min,max);}
        @Override public int subtractSizeFrom(int n){int result=super.subtractSizeFrom(n);record("subtract",ranges,n,result);return result;}
        @Override public void enumerateValues(Collection<Object> values){super.enumerateValues(values);List<Object> expected=new ArrayList<>();for(Object v:values)expected.add(value(v));record("enumerate",ranges,null,expected);}
    }
    public static class BinaryInterval extends BinaryDataLengthInterval {
        final List<Object> ranges;
        public BinaryInterval(BinaryDataType type,int min,int max){super(type,min,max);ranges=length(type==BinaryDataType.HEX_BINARY?"hexBinary":"base64Binary",min,max);}
        @Override public int subtractSizeFrom(int n){int result=super.subtractSizeFrom(n);record("subtract",ranges,n,result);return result;}
        @Override public void enumerateValues(Collection<Object> values){super.enumerateValues(values);List<Object> expected=new ArrayList<>();for(Object v:values)expected.add(value(v));record("enumerate",ranges,null,expected);}
    }
    public static DateTime parseDateTime(String lexical){DateTime d=DateTime.parse(lexical);record("parse",Collections.emptyList(),literal(lexical,XSD+"dateTime"),d==null?null:value(d));return d;}
    public static BinaryData parseBase64Binary(String lexical){BinaryData d=BinaryData.parseBase64Binary(lexical);record("parse",Collections.emptyList(),literal(lexical,XSD+"base64Binary"),d==null?null:value(d));return d;}
    public static class DateInterval extends DateTimeInterval {
        final List<Object> ranges;
        public DateInterval(IntervalType type,long min,BoundType minType,long max,BoundType maxType){
            super(type,min,minType,max,maxType);
            int tz=type==IntervalType.WITH_TIMEZONE?0:DateTime.NO_TIMEZONE;
            DatatypeRestriction dr=DatatypeRestriction.create(XSD+"dateTime",new String[]{XSD+(minType==BoundType.INCLUSIVE?"minInclusive":"minExclusive"),XSD+(maxType==BoundType.INCLUSIVE?"maxInclusive":"maxExclusive")},new Constant[]{Constant.create(new DateTime(min,false,tz).toString(),XSD+"dateTime"),Constant.create(new DateTime(max,false,tz).toString(),XSD+"dateTime")});
            ranges=Arrays.asList(restriction(dr,false));
        }
        @Override public int subtractSizeFrom(int n){int result=super.subtractSizeFrom(n);record("subtract",ranges,n,result);return result;}
        @Override public boolean containsDateTime(DateTime d){boolean result=super.containsDateTime(d);record("contains",ranges,value(d),result);return result;}
        @Override public void enumerateDateTimes(Collection<Object> values){super.enumerateDateTimes(values);List<Object> expected=new ArrayList<>();for(Object v:values)expected.add(value(v));record("enumerate",ranges,null,expected);}
    }
}
