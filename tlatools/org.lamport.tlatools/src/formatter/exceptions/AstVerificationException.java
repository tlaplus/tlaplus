package formatter.exceptions;

import formatter.AstComparator;

/**
 * Thrown when the formatted output's AST does not match the original AST.
 */
public class AstVerificationException extends RuntimeException {
    private final AstComparator.Result result;

    public AstVerificationException(AstComparator.Result result) {
        super(result.formatDiagnostic());
        this.result = result;
    }

    public AstComparator.Result getResult() {
        return result;
    }
}
