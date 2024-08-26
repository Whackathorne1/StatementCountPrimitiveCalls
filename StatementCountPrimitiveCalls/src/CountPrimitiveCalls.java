import components.statement.Statement;

/**
 * Utility class with method to count the number of calls to primitive
 * instructions (move, turnleft, turnright, infect, skip) in a given
 * {@code Statement}.
 *
 * @author Put your name here
 *
 */
public final class CountPrimitiveCalls {

    /**
     * Private constructor so this utility class cannot be instantiated.
     */
    private CountPrimitiveCalls() {
    }

    /**
     * Refactors the given {@code Statement} so that every IF_ELSE statement
     * with a negated condition (NEXT_IS_NOT_EMPTY, NEXT_IS_NOT_ENEMY,
     * NEXT_IS_NOT_FRIEND, NEXT_IS_NOT_WALL) is replaced by an equivalent
     * IF_ELSE with the opposite condition and the "then" and "else" BLOCKs
     * switched. Every other statement is left unmodified.
     *
     * @param s
     *            the {@code Statement}
     * @updates s
     * @ensures <pre>
     * s = [#s refactored so that IF_ELSE statements with "not"
     *   conditions are simplified so the "not" is removed]
     * </pre>
     */
    public static void simplifyIfElse(Statement s) {
        switch (s.kind()) {
            case BLOCK: {
                int length = s.lengthOfBlock();
                for (int i = 0; i < length; i++) {
                    Statement subLabel = s.removeFromBlock(i);
                    simplifyIfElse(subLabel);
                    s.addToBlock(i, subLabel);
                }
                break;
            }
            case IF: {
                Statement subLabel = s.newInstance();
                Statement.Condition condition = s.disassembleIf(subLabel);
                simplifyIfElse(subLabel);
                s.assembleIf(condition, subLabel);
                break;
            }
            case IF_ELSE: {
                Statement subIf = s.newInstance();
                Statement subIfElse = s.newInstance();
                Statement.Condition condition = s.disassembleIfElse(subIf,
                        subIfElse);
                switch (condition.name()) {
                    case "NEXT_IS_NOT_EMPTY": {
                        condition = condition.NEXT_IS_EMPTY;
                        simplifyIfElse(subIf);
                        simplifyIfElse(subIfElse);
                        s.assembleIfElse(condition, subIf, subIfElse);
                        break;
                    }
                    case "NEXT_IS_NOT_WALL": {
                        condition = condition.NEXT_IS_WALL;
                        simplifyIfElse(subIf);
                        simplifyIfElse(subIfElse);
                        s.assembleIfElse(condition, subIf, subIfElse);
                        break;
                    }
                    case "NEXT_IS_NOT_FRIEND": {
                        condition = condition.NEXT_IS_FRIEND;
                        simplifyIfElse(subIf);
                        simplifyIfElse(subIfElse);
                        s.assembleIfElse(condition, subIf, subIfElse);
                        break;
                    }
                    case "NEXT_IS_NOT_ENEMY": {
                        condition = condition.NEXT_IS_ENEMY;
                        simplifyIfElse(subIf);
                        simplifyIfElse(subIfElse);
                        s.assembleIfElse(condition, subIf, subIfElse);
                        break;
                    }
                    default: {
                        break;
                    }
                }
                break;
            }
            case WHILE: {
                Statement subLabel = s.newInstance();
                Statement.Condition condition = s.disassembleWhile(subLabel);
                simplifyIfElse(subLabel);
                s.assembleWhile(condition, subLabel);
                break;
            }
            case CALL: {
                // nothing to do here...can you explain why?
                break;
            }
            default: {
                // this will never happen...can you explain why?
                break;
            }
        }

    }

    /**
     * Reports the number of calls to primitive instructions (move, turnleft,
     * turn-right, infect, skip) in a given {@code Statement}.
     *
     * @param s
     *            the {@code Statement}
     * @return the number of calls to primitive instructions in {@code s}
     * @ensures <pre>
     * countOfPrimitiveCalls =
     *  [number of calls to primitive instructions in s]
     * </pre>
     */
    public static int countOfPrimitiveCalls(Statement s) {
        int count = 0;
        switch (s.kind()) {
            case BLOCK: {
                /*
                 * Add up the number of calls to primitive instructions in each
                 * nested statement in the BLOCK.
                 */
                int length = s.lengthOfBlock();
                for (int i = 0; i < length; i++) {
                    Statement subLabel = s.removeFromBlock(i);
                    count += countOfPrimitiveCalls(subLabel);
                    s.addToBlock(i, subLabel);
                }
                break;
            }
            case IF: {
                /*
                 * Find the number of calls to primitive instructions in the
                 * body of the IF.
                 */
                Statement subLabel = s.newInstance();
                Statement.Condition condition = s.disassembleIf(subLabel);
                count = countOfPrimitiveCalls(subLabel);
                s.assembleIf(condition, subLabel);
                break;
            }
            case IF_ELSE: {
                /*
                 * Add up the number of calls to primitive instructions in the
                 * "then" and "else" bodies of the IF_ELSE.
                 */
                Statement subIf = s.newInstance();
                Statement subIfElse = s.newInstance();
                Statement.Condition condition = s.disassembleIfElse(subIf,
                        subIfElse);
                count = countOfPrimitiveCalls(subIf)
                        + countOfPrimitiveCalls(subIfElse);
                s.assembleIfElse(condition, subIf, subIfElse);
                break;
            }
            case WHILE: {
                /*
                 * Find the number of calls to primitive instructions in the
                 * body of the WHILE.
                 */
                Statement subWhile = s.newInstance();
                Statement.Condition condition = s.disassembleWhile(subWhile);
                count = countOfPrimitiveCalls(subWhile);
                s.assembleWhile(condition, subWhile);
                break;
            }
            case CALL: {
                /*
                 * This is a leaf: the count can only be 1 or 0. Determine
                 * whether this is a call to a primitive instruction or not.
                 */
                String label = s.disassembleCall();
                if (label.equals("turnright") || label.equals("turnleft")
                        || label.equals("infect") || label.equals("move")
                        || label.equals("skip")) {
                    count++;
                }
                s.assembleCall(label);
                break;
            }
            default: {
                // this will never happen...can you explain why?
                break;
            }
        }
        return count;
    }
}
