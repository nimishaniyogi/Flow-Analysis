
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import soot.G;
import soot.Local;
import soot.RefLikeType;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.NewExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import soot.util.Debug;

/** LocalNotMayAliasAnalysis attempts to determine if two local
 * variables (at two potentially different program points) definitely
 * point to different objects.
 *
 * The underlying abstraction is that of definition expressions.  When
 * a local variable gets assigned a new object (unlike LocalMust, only
 * NewExprs), the analysis tracks the source of the value. If two
 * variables have different sources, then they are different.
 * 
 * See Sable TR 2007-8 for details.
 * 
 * @author Patrick Lam
 */
public class LocalMustNotAliasAnalysis extends ForwardFlowAnalysis
{
    protected static final Object UNKNOWN = new Object() {
        public String toString() {
//        	G.v().out.println("\nFrom LocalMust inside object\n");
            return "UNKNOWN";
        }
    };
    
    protected List<Local> locals;

    public LocalMustNotAliasAnalysis(UnitGraph g)
    {
        super(g);
        locals = new LinkedList<Local>(); locals.addAll(g.getBody().getLocals());
        
//        G.v().out.println("\nFrom LocalMust inside constructor -- 1\n");
        
        for (Local l : (Collection<Local>) g.getBody().getLocals()) {
//        	G.v().out.println("\nFrom LocalMust inside constructor -- for\n");
            if (l.getType() instanceof RefLikeType)
//            	G.v().out.println("\nFrom LocalMust inside constructor -- if\n");
                locals.add(l);
        }
//        G.v().out.println("\nFrom LocalMust proceeding to doAnalysis \n");
        doAnalysis();
//        G.v().out.println("\nFrom LocalMust returned from doAnalysis \n");
    }

    @SuppressWarnings({ "rawtypes", "unchecked" })
	protected void merge(Object in1, Object in2, Object o)
    {
        HashMap inMap1 = (HashMap) in1;
        HashMap inMap2 = (HashMap) in2;
        HashMap outMap = (HashMap) o;

//        G.v().out.println("\nFrom LocalMust inside merge \n");
        
        for (Local l : locals) {
            Set l1 = (Set)inMap1.get(l), l2 = (Set)inMap2.get(l);
            Set out = (Set)outMap.get(l);
//            G.v().out.println("\n From LocalMust inside merge inside for \n");
            out.clear();
            if (l1.contains(UNKNOWN) || l2.contains(UNKNOWN)) {
                out.add(UNKNOWN);
//                G.v().out.println("\n From LocalMust inside merge inside for inside if\n");
            } else {
                out.addAll(l1); out.addAll(l2);
//                G.v().out.println("\n From LocalMust inside merge inside for inside else\n");
            }
        }
      
    }
    

    @SuppressWarnings({ "rawtypes", "unchecked" })
	protected void flowThrough(Object inValue, Object unit, Object outValue)
    {
//    	G.v().out.println("\n From LocalMust inside flowThrough \n");
        HashMap     in  = (HashMap) inValue;
        HashMap     out = (HashMap) outValue;
        Stmt    s   = (Stmt)    unit;

        out.clear();
        out.putAll(in);

        if (s instanceof DefinitionStmt) {
//        	G.v().out.println("\n From LocalMust inside flowThrough inside if -- 1 \n");
            DefinitionStmt ds = (DefinitionStmt) s;
            Value lhs = ds.getLeftOp();
            Value rhs = ds.getRightOp();
            if (lhs instanceof Local) {
//            	G.v().out.println("\n From LocalMust inside flowThrough inside if -- 2 \n");
                HashSet lv = new HashSet();
                out.put(lhs, lv);
                if (rhs instanceof NewExpr) {
//                	G.v().out.println("\n From LocalMust inside flowThrough inside if -- 3 \n");
                    lv.add(rhs);
                } else if (rhs instanceof Local) {
//                	G.v().out.println("\n From LocalMust inside flowThrough inside if -- 4 \n");
                    lv.addAll((HashSet)in.get(rhs));
                } else lv.add(UNKNOWN);
            }
        }
        if(s instanceof JAssignStmt) {
//        	G.v().out.println("\n From LocalMust inside flowThrough inside if -- 5 \n");
        	JAssignStmt js = (JAssignStmt) s;
        	Value lhs = js.getLeftOp();
//        	G.v().out.println("\nThe value in js.getLeftOp() is : " + js.getLeftOp());
//        	G.v().out.println("\nThe value of lhs is : " + lhs);
    		Value rhs = js.getRightOp();
//    		G.v().out.println("\nThe value in js.getRightOP() is : " + js.getRightOp());
//        	G.v().out.println("\nThe value of rhs is : " + rhs);
        	if(lhs instanceof ArrayRef){
//        		G.v().out.println("\n From LocalMust inside flowThrough inside if -- 6 \n");
        		G.v().out.println("Statement " +lhs.toString() + " = " + rhs.toString() + ",\t\t\t heap write");
        	}
        	if(rhs instanceof ArrayRef){
//        		G.v().out.println("\n From LocalMust inside flowThrough inside if -- 7 \n");
        		G.v().out.println("Statement " + lhs.toString() + " = " + rhs.toString() + ",\t\t\t heap read");
        	}
        	
        	if(lhs instanceof InstanceFieldRef){
//        		G.v().out.println("\n From LocalMust inside flowThrough inside if -- 8 \n");
        		G.v().out.println("Statement " +lhs.toString() + " = " + rhs.toString() + ",\t\t heap write");
        	}
        	if(rhs instanceof InstanceFieldRef){
//        		G.v().out.println("\n From LocalMust inside flowThrough inside if -- 9 \n");
        		G.v().out.println("Statement " +lhs.toString() + " = " + rhs.toString() + ",\t\t heap read");
        	}
        	
        	if(lhs instanceof StaticFieldRef){
//        		G.v().out.println("\n From LocalMust inside flowThrough inside if -- 10 \n");
        		G.v().out.println("Statement " +lhs.toString() + " = " + rhs.toString() + ",\t\t\t heap write");
        	}
        	if(rhs instanceof StaticFieldRef){
//        		G.v().out.println("\n From LocalMust inside flowThrough inside if -- 11 \n");
        		G.v().out.println("Statement " +lhs.toString() + " = " + rhs.toString() + ",\t heap read");
        	}
        }
    }

    @SuppressWarnings({ "unchecked", "rawtypes" })
	protected void copy(Object source, Object dest)
    {
        HashMap sourceMap = (HashMap) source;
        HashMap destMap   = (HashMap) dest;
            
        destMap.putAll(sourceMap);
    }

    @SuppressWarnings({ "unchecked", "rawtypes" })
	protected Object entryInitialFlow()
    {
        HashMap m = new HashMap();
        for (Local l : (Collection<Local>) locals) {
            HashSet s = new HashSet(); s.add(UNKNOWN);
            m.put(l, s);
        }
        return m;
    }
        
    @SuppressWarnings({ "unchecked", "rawtypes" })
	protected Object newInitialFlow()
    {
        HashMap m = new HashMap();
        for (Local l : (Collection<Local>) locals) {
            HashSet s = new HashSet(); 
            m.put(l, s);
        }
        return m;
    }

    /**
     * Returns true if this analysis has any information about local l
     * at statement s (i.e. it is not {@link #UNKNOWN}).
     * In particular, it is safe to pass in locals/statements that are not
     * even part of the right method. In those cases <code>false</code>
     * will be returned.
     * Permits s to be <code>null</code>, in which case <code>false</code> will be returned.
     */
    @SuppressWarnings({ "rawtypes", "unchecked" })
	public boolean hasInfoOn(Local l, Stmt s) {
    	HashMap flowBefore = (HashMap) getFlowBefore(s);
    	if(flowBefore==null) {
    		return false;
    	} else {
    		Set info = (Set) flowBefore.get(l);
    		return info!=null && !info.contains(UNKNOWN);
    	}
    }

    /**
     * @return true if values of l1 (at s1) and l2 (at s2) are known
     * to point to different objects
     */
    @SuppressWarnings({ "rawtypes", "unchecked" })
	public boolean notMayAlias(Local l1, Stmt s1, Local l2, Stmt s2) {
        Set l1n = (Set) ((HashMap)getFlowBefore(s1)).get(l1);
        Set l2n = (Set) ((HashMap)getFlowBefore(s2)).get(l2);

        if (l1n.contains(UNKNOWN) || l2n.contains(UNKNOWN))
            return false;

        Set n = new HashSet(); n.addAll(l1n); n.retainAll(l2n);
        return n.isEmpty();
    }
        
}