/**
 * BSD-style license; for more info see http://pmd.sourceforge.net/license.html
 */

package net.sourceforge.pmd.lang.python;

import java.io.Reader;

import net.sourceforge.pmd.lang.TokenManager;
import net.sourceforge.pmd.lang.ast.impl.javacc.CharStreamFactory;
import net.sourceforge.pmd.lang.python.ast.PythonParserTokenManager;

/**
 * Python Token Manager implementation.
 */
public class PythonTokenManager implements TokenManager {
    private final PythonParserTokenManager tokenManager;

    /**
     * Creates a new Python Token Manager from the given source code.
     *
     * @param source
     *            the source code
     */
    public PythonTokenManager(Reader source) {
        tokenManager = new PythonParserTokenManager(CharStreamFactory.simpleCharStream(source));
    }

    @Override
    public Object getNextToken() {
        return tokenManager.getNextToken();
    }

    @Override
    public void setFileName(String fileName) {
        PythonParserTokenManager.setFileName(fileName);
    }
}
