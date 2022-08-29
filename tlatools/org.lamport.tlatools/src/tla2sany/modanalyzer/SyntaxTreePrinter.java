// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import tla2sany.st.Location;
import tla2sany.st.ParseTree;
import tla2sany.st.TreeNode;

import java.util.Objects;

public class SyntaxTreePrinter {

    /**
     * This method is used in only one place--in the ParseUnit class--to write a copy
     * of the syntax tree to a file in case that option is invoked.
     */
    public static void print(final ParseTree pt, final java.io.PrintWriter output) {
        output.println("%% Output of parse tree for module " + pt.moduleName());
        final String[] dependencies = pt.dependencies();
        if (dependencies.length == 0) {
            output.println("%% no dependencies");
        } else {
            output.print("%% dependends on:");
            for (final String dependency : dependencies) {
                output.print(" " + dependency);
            }
            output.println(".");
        }
        printSubTree(output, "", pt.rootNode());
    }

    private static void printSubTree(final java.io.PrintWriter o, final String offset, final TreeNode node) {
        final StringBuilder outS = new StringBuilder(offset);
        final Location l = node.getLocation();
        final String image = node.getImage();
        outS.append(Objects.requireNonNullElse(image, "-- no name --"));
        outS.append(" [").append(l.beginLine()).append(" ").append(l.beginColumn()).append("] ");
        final TreeNode[] h = node.heirs();
// ADDED BY LL
// if (h == null) {
        outS.append(" (kind: ").append(node.getKind()).append(") ");
// } ;
// END ADDED BY LL
        if (h != null) {
            if (h.length == 0) {
                final int length = node.getPreComments().length;
                outS.append(length);
                outS.append(" pre-comments ");
// Commented out on 21 Aug 2007 by LL
            }
            outS.append(" {");
            o.println(outS);
            for (final TreeNode treeNode : h) {
                printSubTree(o, offset + ".", treeNode);
            }
            o.print(offset);
            o.println("}");
        } else {
            outS.append(" ***WARNING***  null array reference ");
            o.println(outS);
        }
    }

}

