/**
 * BSD-style license; for more info see http://pmd.sourceforge.net/license.html
 */

package net.sourceforge.pmd.lang.plsql;

import java.io.Reader;

import net.sourceforge.pmd.lang.TokenManager;
import net.sourceforge.pmd.lang.ast.impl.javacc.CharStreamFactory;
import net.sourceforge.pmd.lang.plsql.ast.PLSQLParserTokenManager;

/**
 * PLSQL Token Manager implementation.
 */
public class PLSQLTokenManager implements TokenManager {
    private final PLSQLParserTokenManager tokenManager;

    public PLSQLTokenManager(Reader source) {
        tokenManager = new PLSQLParserTokenManager(CharStreamFactory.simpleCharStream(source));
    }

    @Override
    public Object getNextToken() {
        return tokenManager.getNextToken();
    }

    @Override
    public void setFileName(String fileName) {
        PLSQLParserTokenManager.setFileName(fileName);
    }
}
