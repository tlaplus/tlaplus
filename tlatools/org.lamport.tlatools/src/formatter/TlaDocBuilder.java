package formatter;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.ConstructRegistry;
import formatter.constructs.TlaConstruct;
import formatter.constructs.impl.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * New registry-based implementation of TlaDocBuilder.
 * Uses a plugin system for handling different TLA+ constructs.
 */
public class TlaDocBuilder {

    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    private final ConstructRegistry registry;
    private final ConstructContext context;
    private String originalSource;

    public TlaDocBuilder(FormatConfig config) {
        this.registry = new ConstructRegistry();
        this.context = new ConstructContext(config, this);
        registerDefaultConstructs();
    }

    /**
     * Register all default TLA+ constructs.
     */
    private void registerDefaultConstructs() {
        // Module structure
        registry.register(new ModuleConstruct.ModuleMainConstruct());
        registry.register(new ModuleConstruct.BeginModuleConstruct());
        registry.register(new ModuleConstruct.EndModuleConstruct());
        registry.register(new ModuleConstruct.BodyConstruct());

        // Declarations
        registry.register(new ExtendsConstruct());
        registry.register(new ConstantsConstruct());
        registry.register(new VariableConstruct());
        registry.register(new OperatorConstruct());
        registry.register(new ConstantConstruct());
        registry.register(new InfixLhsConstruct());

        // Basic elements
        registry.register(new IdentifierConstruct());
        registry.register(new NumberConstruct());
        registry.register(new StringConstruct());
        registry.register(new TheoremConstruct());
        registry.register(new FcnApplConstruct());
        registry.register(new QuantBoundConstruct());
        registry.register(new FcnConstConstruct());
        registry.register(new OpArgsConstruct());
        registry.register(new OpApplicationConstruct());
        registry.register(new BoundedQuantConstruct());
        registry.register(new MaybeBoundConstruct());
        registry.register(new IdentLHSConstruct());
        registry.register(new IdentDeclConstruct());
        registry.register(new SetOfFcnsConstruct());
        registry.register(new PrefixExprConstruct());
        registry.register(new GenInfixOp());
        registry.register(new RecursiveConstruct());
        registry.register(new LetInConstruct());
        registry.register(new LetDefinitionsConstruct());
        registry.register(new DisjListConstruct());
        registry.register(new DisjItemConstruct());
        registry.register(new ConjItemConstruct());
        registry.register(new ConjListConstruct());
        registry.register(new AssumptionConstruct());
        registry.register(new PostfixExprConstruct());
        registry.register(new GenPostfixOpConstruct());
        registry.register(new SubsetOfConstruct());
        registry.register(new SetOfAllConstruct());
        registry.register(new ExceptComponentConstruct());
        registry.register(new ExceptConstruct());
        registry.register(new ExceptSpecConstruct());
        registry.register(new UnboundedOrBoundedChooseConstruct());
        registry.register(new RecordComponentConstruct());
        registry.register(new FieldSetConstruct());
        registry.register(new ActionExpr());
        registry.register(new CaseArmConstruct());
        registry.register(new CaseConstruct());
        registry.register(new FunctionDefinitionConstruct());
        registry.register(new SetOfRcdsConstruct());
        registry.register(new OtherArmConstruct());
        registry.register(new IdentifierTuple());
        registry.register(new FairnessExprConstruct());
        registry.register(new LambdaConstruct());

        // Expressions
        registry.register(new IfThenElseConstruct());
        registry.register(new ParenExprConstruct());
        registry.register(new InfixExprConstruct());
        registry.register(new GenInfixOpConstruct());
        registry.register(new RcdConstructorConstruct());
        registry.register(new FieldValConstruct());
        registry.register(new TupleConstruct());
        registry.register(new SetEnumerateConstruct());
        registry.register(new TimesConstruct());
        registry.register(new IdPrefixConstruct());
        registry.register(new InstanceConstruct());
        registry.register(new InstanceConstruct.NonLocalInstanceConstruct());

        // Proofs
        registry.register(new ProofConstruct());
        registry.register(new ProofConstruct.InnerProofConstruct());
        registry.register(new ProofConstruct.ProofStepConstruct());
        registry.register(new DefStepConstruct());
        registry.register(new AssumeProveConstruct());
        registry.register(new PickStepConstruct());

    }

    /**
     * Main build method - now uses the registry system.
     */
    public Doc build(TreeNode node) {
        if (node == null) {
            return Doc.empty();
        }

        // Try to find a registered construct handler
        TlaConstruct construct = registry.findHandler(node);
        if (construct != null) {
            try {
                //LOG.debug("Calling {}: '{}'", construct.getName(), node.getHumanReadableImage());
                var indentSize = context.getConfig().getIndentSize();
                return construct.buildDoc(node, context, indentSize);
            } catch (Exception e) {
                LOG.warn("Error building doc for construct {} on node kind {}: {}",
                        construct.getName(), node.getKind(), e.getMessage(), e);
                // Fall back to generic handling
            }
        }

        // Fall back to generic handling
        return buildGeneric(node);
    }

    /**
     * Get the best available image string from a node.
     * Uses getHumanReadableImage() if non-empty, otherwise falls back to getImage().
     * This is needed because SANY returns empty getHumanReadableImage() for certain
     * keywords/tokens like "Token" even though getImage() has the correct value.
     */
    public static String getBestImage(TreeNode node) {
        String hri = node.getHumanReadableImage();
        if (hri != null && !hri.isEmpty()) {
            return hri;
        }
        return node.getImage();
    }

    /**
     * Generic fallback handling for unknown node types.
     * This preserves the original behavior for unhandled nodes.
     */
    private Doc buildGeneric(TreeNode node) {
        String image = node.getImage();

        // Log unknown node types to help with future construct development
        if (image != null && image.startsWith("N_")) {
            LOG.debug("Generic node kind: {} image: '{}' hri: '{}'", node.getKind(), image, node.getHumanReadableImage());
        }

        // Leaf nodes (no children) are always rendered as text, even if image
        // starts with "N_" -- user identifiers like "N_Assumption" must not be
        // confused with SANY internal node kind names.
        boolean isLeaf = (node.zero() == null || node.zero().length == 0)
                      && (node.one() == null || node.one().length == 0);
        if (image != null && !image.isEmpty() && (isLeaf || !image.startsWith("N_"))) {
            return Doc.text(getBestImage(node));
        }

        // If no meaningful image, try to build from children
        List<Doc> children = new ArrayList<>();

        if (node.zero() != null) {
            for (TreeNode child : node.zero()) {
                if (isValidNode(child)) {
                    Doc childDoc = context.buildChild(child);
                    children.add(childDoc);
                }
            }
        }

        if (node.one() != null) {
            for (TreeNode child : node.one()) {
                if (isValidNode(child)) {
                    Doc childDoc = context.buildChild(child);
                    children.add(childDoc);
                }
            }
        }

        if (children.isEmpty()) {
            return Doc.empty();
        }

        // Join children with spaces
        Doc result = children.get(0);
        for (int i = 1; i < children.size(); i++) {
            result = result.appendSpace(children.get(i));
        }

        return result;
    }

    /**
     * Checks if a node is valid (has a real location, not a placeholder).
     */
    private boolean isValidNode(TreeNode node) {
        if (node == null) {
            return false;
        }

        // SANY creates placeholder nodes with MAX_VALUE coordinates
        return node.getLocation() != null &&
                node.getLocation().beginLine() != Integer.MAX_VALUE;
    }

    /**
     * Set the original source content for spacing preservation.
     */
    public void setOriginalSource(String source) {
        this.originalSource = source;
    }

    /**
     * Get preserved spacing after a node based on original source.
     * Returns appropriate Doc for extra newlines between this node and the next.
     */
    public Doc getSpacingAfter(TreeNode node, TreeNode next) {
        if (originalSource == null || node == null || node.getLocation() == null) {
            return Doc.empty();
        }

        int nodeEndLine = node.getLocation().endLine(); // Convert to 0-based index
        int nextStartLine = getBeginLineSkipComments(next);
        if (nodeEndLine == Integer.MAX_VALUE || nextStartLine == Integer.MAX_VALUE) {
            return null;
        }
        // Count consecutive empty lines after this node (starting from the line after the node ends)
        int emptyLines = nextStartLine - nodeEndLine;
        // Return appropriate spacing (preserve extra newlines)
        if (emptyLines == 1) {
            return null;
        }
        Doc result = Doc.empty();
        for (int i = 1; i < emptyLines - 1; i++) {
            result = result.appendLine(Doc.empty());
        }
        return result;
    }

    int getBeginLineSkipComments(TreeNode node) {
        return node.getLocation().beginLine() - getPreCommentsRec(node);
    }

    /**
     * Get the number of pre comment lines, by recursively searching them in the first child.
     * It's used in the format method to respect the newlines between different declarations
     * in the module's body.
     *
     * @return the number of preComments, recursively.
     */
    private static int getPreCommentsRec(TreeNode node) {
        if (node.getPreComments().length > 0) {
            // Each entry in PreComments is either a single line comments or a block comment.
            // Block comments are composed of multiple lines, so we need to count them all.
            // TODO: AND single line comments only include a single \n even if there is \* comment\n\n\n\n\n\n=======
            // would be great to fix this in SANY.
            // Alternatively we would need to run a new parsing of the spec, find the actual number of new lines between every line comment and
            // apply them as expected.
            return Arrays.stream(node.getPreComments())
                    .mapToInt(s -> Math.toIntExact(s.lines().count()))
                    .sum();
        }

        if (node.zero() != null && node.zero().length > 0) return getPreCommentsRec(node.zero()[0]);
        if (node.one() != null && node.one().length > 0) return getPreCommentsRec(node.one()[0]);
        return 0;
    }
}