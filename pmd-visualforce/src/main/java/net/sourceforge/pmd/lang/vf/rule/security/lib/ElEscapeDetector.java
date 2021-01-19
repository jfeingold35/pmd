/**
 * BSD-style license; for more info see http://pmd.sourceforge.net/license.html
 */

package net.sourceforge.pmd.lang.vf.rule.security.lib;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;

import net.sourceforge.pmd.lang.ast.Node;
import net.sourceforge.pmd.lang.vf.DataType;
import net.sourceforge.pmd.lang.vf.ast.ASTArguments;
import net.sourceforge.pmd.lang.vf.ast.ASTDotExpression;
import net.sourceforge.pmd.lang.vf.ast.ASTElExpression;
import net.sourceforge.pmd.lang.vf.ast.ASTExpression;
import net.sourceforge.pmd.lang.vf.ast.ASTIdentifier;
import net.sourceforge.pmd.lang.vf.ast.ASTNegationExpression;
import net.sourceforge.pmd.lang.vf.ast.AbstractVFNode;
import net.sourceforge.pmd.lang.vf.ast.VfNode;
import net.sourceforge.pmd.lang.vf.ast.VfTypedNode;

/**
 * Helps detect visualforce encoding in EL Expressions
 * (porting over code previously living in VfUnescapeElRule for reusability)
 */

public final class ElEscapeDetector {

    public boolean expressionRecursivelyValid(final ASTExpression expression, final EnumSet<Escaping> escapes) {
        // We'll want to iterate over all of this expression's children.
        int childCount = expression.getNumChildren();
        String prevId = "";
        List<ASTExpression> relevantChildren = new ArrayList<>();
        for (int i = 0; i < childCount; i++) {
            Node child = expression.getChild(i);

            if (child instanceof ASTIdentifier) {
                // How we deal with an Identifier depends on what the next node after it is.
                if (i < childCount - 1) {
                    VfNode nextNode = expression.getChild(i + 1);
                    // If the next node is Arguments or a Dot expression, that means this Identifier represents the name
                    // of a function, or some kind of object. In that case, we might be okay. So we'll store the name
                    // and keep going.
                    if (nextNode instanceof ASTArguments || nextNode instanceof ASTDotExpression) {
                        prevId = child.getImage();
                        continue;
                    }
                }
                // If there's no next node, or the next node isn't of one of those types, then this Identifier is a raw
                // variable, which is dangerous. So we must return false.
                return false;
            } else if (child instanceof ASTArguments) {
                // An Arguments node means we're looking at some kind of function call.
                // If it's one of our designated escape functions, we're in the clear and we can keep going.
                // Also, some built-in functions are inherently safe, which would mean we're good to continue.
                if (functionIsEscape(prevId, escapes) || functionInherentlySafe(prevId)) {
                    continue;
                }

                // Otherwise, identify the argument expressions that must be checked, and add them to the list.
                relevantChildren.addAll(getXssableArguments(prevId, (ASTArguments) child));
            } else if (child instanceof ASTDotExpression) {
                // Dot expressions mean we're doing accessing properties of variables.
                // If the variable is one of the definitely-safe global variables, then we're in the clear.
                if (isSafeGlobal(prevId)) {
                    continue;
                }
                // If the node after this one is also a Dot expression, then this is a chained access, and we can't make
                // any final judgements.
                if (i < childCount - 1 && expression.getChild(i + 1) instanceof ASTDotExpression) {
                    continue;
                }
                // If none of those things are true, then we need to determine whether the field being accessed is
                // definitely safe.
                ASTIdentifier propId = child.getFirstChildOfType(ASTIdentifier.class);
                // If the field isn't definitely safe, then it ought to be escaped. Return false.
                if (!isSafeField(propId.getImage())) {
                    return false;
                }
            } else if (child instanceof ASTExpression) {
                // Expressions should always be added to the list.
                relevantChildren.add((ASTExpression) child);
            }
        }
        // Just because there's nothing immediately wrong with this node doesn't mean its children are guaranteed to be
        // fine. Iterate over all of the children and make a recursive call. If any of those calls return false, we need
        // to relay that back up the chain.
        for (ASTExpression e : relevantChildren) {
            if (!expressionRecursivelyValid(e, escapes)) {
                return false;
            }
        }
        // If we didn't find a reason to return false, we're good. Return true.
        return true;
    }

    private boolean functionIsEscape(String functionName, EnumSet<Escaping> escapes) {
        // If one of the escapes we were passed is ANY, use a set that contains all options.
        EnumSet<Escaping> handledEscapes = escapes.contains(Escaping.ANY) ? EnumSet.allOf(Escaping.class) : escapes;
        for (Escaping e : handledEscapes) {
            if (functionName.equalsIgnoreCase(e.toString())) {
                return true;
            }
        }
        return false;
    }

    private boolean functionInherentlySafe(String functionName) {
        String lowerCaseName = functionName.toLowerCase(Locale.ROOT);
        switch (lowerCaseName) {
        // These are all of the date-time functions, which don't require escaping because they either accept or return dates.
        case "addmonths":
        case "date":
        case "datevalue":
        case "datetimevalue":
        case "day":
        case "hour":
        case "millisecond":
        case "minute":
        case "month":
        case "now":
        case "second":
        case "timenow":
        case "timevalue":
        case "today":
        case "weekday":
        case "year":
        // These are all of the logical functions that return booleans, which are definitionally safe.
        case "and":
        case "isblank":
        case "isclone":
        case "isnew":
        case "isnull":
        case "isnumber":
        case "not":
        case "or":
        // These are all of the math functions, which are definitionally safe since they return numbers.
        case "abs":
        case "ceiling":
        case "exp":
        case "floor":
        case "ln":
        case "log":
        case "max":
        case "mceiling":
        case "mfloor":
        case "min":
        case "mod":
        case "round":
        case "sqrt":
        // These text functions are safe, either because of what they return or because of what they accept.
        case "begins":
        case "br":
        case "casesafeid":
        case "contains":
        case "find":
        case "getsessionid":
        case "ispickval":
        case "len":
        // These advanced functions are safe because of what they accept or what they return.
        case "currencyrate":
        case "getrecordids":
        case "ischanged":
        case "junctionidlist":
        case "regex":
        case "urlfor":
            return true;
        default:
            // Other functions cannot be assumed to be safe.
            return false;
        }
    }

    private List<ASTExpression> getXssableArguments(String functionName, ASTArguments arguments) {
        List<ASTExpression> exprs = new ArrayList<>();
        int argCount = arguments.getNumChildren();
        if (argCount != 0) {
            String lowerCaseName = functionName.toLowerCase(Locale.ROOT);
            List<Integer> indicesToCheck = new ArrayList<>();

            // See if the function name corresponds to one of the built-in functions that don't require us to examine
            // every argument.
            switch (lowerCaseName) {
            // For these logical functions, we only want to examine certain arguments.
            case "case":     // (exp, val1, res1, val2, res2, ...else-res). We care about the resX and else-res arguments.
                for (int i = 2; i < argCount; i += 2) {
                    indicesToCheck.add(i);
                }
                indicesToCheck.add(argCount - 1);
                break;
            case "if":       // (test, pass, fail). We care about pass and fail, since those are the returned values.
                indicesToCheck.add(1);
                indicesToCheck.add(2);
                break;
            // For these text functions, we only want to examine certain arguments.
            case "left":     // (text, num_chars). We care about the text.
            case "lower":    // (text[, locale]). We care about the text.
            case "mid":      // (text, start, len). We care about the text.
            case "right":    // (text, num_chars). We care about the text.
            case "upper":    // (text[, locale]). We care about the text.
                indicesToCheck.add(0);
                break;
            case "lpad":     // (text, padded_length[, pad_string]). We care about the text and the pad_string.
            case "rpad":     // (text, padded_length[, pad_string]). We care about the text and the pad_string.
                indicesToCheck.add(0);
                if (argCount == 3) {
                    indicesToCheck.add(2);
                }
                break;
            // All other functions, we want to examine every argument.
            default:
                for (int i = 0; i < argCount; i++) {
                    indicesToCheck.add(i);
                }
                break;
            }

            // Add each of the targeted arguments to the return array if they represent an Expression node. (They always
            // should, but better safe than sorry.)
            for (int i : indicesToCheck) {
                VfNode ithArg = arguments.getChild(i);
                if (ithArg instanceof ASTExpression) {
                    exprs.add((ASTExpression) ithArg);
                }
            }
        }
        return exprs;
    }

    private boolean isSafeGlobal(String id) {
        String lowerCaseId = id.toLowerCase(Locale.ROOT);
        switch (lowerCaseId) {
        case "$action":
        case "$page":
        case "$site":
        case "$resource":
        case "$label":
        case "$objecttype":
        case "$component":
        case "$remoteaction":
        case "$messagechannel":
            return true;
        default:
            return false;
        }
    }

    private boolean isSafeField(String fieldName) {
        String lowerCaseName = fieldName.toLowerCase(Locale.ROOT);
        switch (lowerCaseName) {
        case "id":
        case "size":
        case "casenumber":
            return true;
        default:
            return false;
        }
    }


    public boolean innerContainsSafeFields(final AbstractVFNode expression) {
        for (int i = 0; i < expression.getNumChildren(); i++) {
            Node child = expression.getChild(i);

            if (child instanceof ASTIdentifier) {
                switch (child.getImage().toLowerCase(Locale.ROOT)) {
                case "id":
                case "size":
                case "caseNumber":
                    return true;
                default:
                }
            }

            if (child instanceof ASTArguments) {
                if (containsSafeFields((ASTArguments) child)) {
                    return true;
                }
            }

            if (child instanceof ASTDotExpression) {
                if (innerContainsSafeFields((ASTDotExpression) child)) {
                    return true;
                }
            }

        }

        return false;
    }

    public boolean containsSafeFields(final AbstractVFNode expression) {
        final ASTExpression ex = expression.getFirstChildOfType(ASTExpression.class);

        return ex != null && innerContainsSafeFields(ex);

    }

    public boolean startsWithSafeResource(final ASTElExpression el) {
        final ASTExpression expression = el.getFirstChildOfType(ASTExpression.class);
        if (expression != null) {
            final ASTNegationExpression negation = expression.getFirstChildOfType(ASTNegationExpression.class);
            if (negation != null) {
                return true;
            }

            final ASTIdentifier id = expression.getFirstChildOfType(ASTIdentifier.class);
            if (id != null) {
                List<ASTArguments> args = expression.findChildrenOfType(ASTArguments.class);

                if (!args.isEmpty()) {
                    return functionInherentlySafe(id.getImage());
                } else {
                    return isSafeGlobal(id.getImage());
                }
            }
        }
        return false;
    }

    public boolean doesElContainAnyUnescapedIdentifiers(final ASTElExpression elExpression, Escaping escape) {
        return doesElContainAnyUnescapedIdentifiers(elExpression, EnumSet.of(escape));

    }

    public boolean doesElContainAnyUnescapedIdentifiers(final ASTElExpression elExpression,
                                                         EnumSet<Escaping> escapes) {
        if (elExpression == null) {
            return false;
        }

        final Set<ASTIdentifier> nonEscapedIds = new HashSet<>();

        final List<ASTExpression> exprs = elExpression.findChildrenOfType(ASTExpression.class);
        for (final ASTExpression expr : exprs) {

            if (innerContainsSafeFields(expr)) {
                continue;
            }

            if (expressionContainsSafeDataNodes(expr)) {
                continue;
            }

            final List<ASTIdentifier> ids = expr.findChildrenOfType(ASTIdentifier.class);
            for (final ASTIdentifier id : ids) {
                boolean isEscaped = false;

                for (Escaping e : escapes) {

                    if (id.getImage().equalsIgnoreCase(e.toString())) {
                        isEscaped = true;
                        break;
                    }

                    if (e.equals(Escaping.ANY)) {
                        for (Escaping esc : Escaping.values()) {
                            if (id.getImage().equalsIgnoreCase(esc.toString())) {
                                isEscaped = true;
                                break;
                            }
                        }
                    }

                }

                if (!isEscaped) {
                    nonEscapedIds.add(id);
                }
            }

        }

        return !nonEscapedIds.isEmpty();
    }

    /**
     * Return true if the type of all data nodes can be determined and none of them require escaping
     * @param expression
     */
    public boolean expressionContainsSafeDataNodes(ASTExpression expression) {
        try {
            for (VfTypedNode node : expression.getDataNodes().keySet()) {
                DataType dataType = node.getDataType();
                if (dataType == null || dataType.requiresEscaping) {
                    return false;
                }
            }

            return true;
        } catch (ASTExpression.DataNodeStateException e) {
            return false;
        }
    }

    public enum Escaping {
        HTMLENCODE("HTMLENCODE"),
        URLENCODE("URLENCODE"),
        JSINHTMLENCODE("JSINHTMLENCODE"),
        JSENCODE("JSENCODE"),
        ANY("ANY");

        private final String text;

        Escaping(final String text) {
            this.text = text;
        }

        @Override
        public String toString() {
            return text;
        }
    }

}
