<blockquote><code><b>\n</b></code><br>
<code>funcdef</code> <code>'createBalance'</code> <code>::</code> <code>'Numerical'</code> <code>→</code> <code>[</code> <code>'Balance'</code> <code>]</code> <code><b>\n</b></code><br>
<code>funcdef</code> <code>'createBalance'</code> <code>'bal'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>let</code> <code>'new_bal'</code> <code>as</code> <code>'Balance'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>set</code> <code>'new_bal'</code> <code>as</code> <code>NUMERICAL_LITERAL</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>trycast</code> <code>'bal'</code> <code>into</code> <code>'new_bal'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>on</code> <code>NUMERICAL_LITERAL</code> <code>→</code> <code>set</code> <code>'new_bal'</code> <code>as</code> <code>'bal'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>on</code> <code>NUMERICAL_LITERAL</code> <code>→</code> <code>set</code> <code>'bal'</code> <code>as</code> <code>NUMERICAL_LITERAL</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>do</code> <code>'bal'</code> <code><=</code> <code>NUMERICAL_LITERAL</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>on</code> <code>NUMERICAL_LITERAL</code> <code>→</code> <code>set</code> <code>'bal'</code> <code>as</code> <code>NUMERICAL_LITERAL</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'return'</code> <code>(</code> <code>'new_bal'</code> <code>)</code> <code><b>\n</b></code><br>
<code>suchthat</code> <code>:</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>|</code> <code>'doc'</code> <code>as</code> <code>STRING_LITERAL</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>|</code> <code>'doc'</code> <code>'bal'</code> <code>as</code> <code>STRING_LITERAL</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>|</code> <code>'web'</code> <code>as</code> <code>STRING_LITERAL</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>|</code> <code>'web'</code> <code>'Currency_Site'</code> <code>as</code> <code>STRING_LITERAL</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>|</code> <code>'example'</code> <code>as</code> <code>STRING_LITERAL</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>|</code> <code>'example'</code> <code>as</code> <code>STRING_LITERAL</code> <code><b>\n</b></code><br>
<code>end</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>funcdef</code> <code>'addToBalance'</code> <code>::</code> <code>'Balance'</code> <code>,</code> <code>'Numerical'</code> <code>→</code> <code>'Balance'</code> <code><b>\n</b></code><br>
<code>funcdef</code> <code>'addToBalance'</code> <code>'bal'</code> <code>'amount'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'return'</code> <code>(</code> <code>'createBalance'</code> <code>(</code> <code>'bal'</code> <code>+</code> <code>'amount'</code> <code>)</code> <code>)</code> <code><b>\n</b></code><br>
<code>suchthat</code> <code>:</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>|</code> <code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'doc'</code> <code>as</code> <code>STRING_LITERAL</code> <code><b>\n</b></code><br>
<code>end</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>typedef</code> <code>'Balance'</code> <code>'a'</code> <code>::</code> <code>'Integer'</code> <code>{</code> <code>NUMERICAL_LITERAL</code> <code><=</code> <code>'a'</code> <code>}</code> <code><b>\n</b></code><br>
<code>suchthat</code> <code>:</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>|</code> <code>'doc'</code> <code>as</code> <code>STRING_LITERAL</code> <code><b>\n</b></code><br>
<code>end</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>typedef</code> <code>'Accounts'</code> <code>'a'</code> <code>::</code> <code>[</code> <code>'Balance'</code> <code>]</code> <code>{</code> <code>NUMERICAL_LITERAL</code> <code><=</code> <code>'a'</code> <code>}</code> <code><b>\n</b></code><br>
<code>suchthat</code> <code>:</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>|</code> <code>'doc'</code> <code>as</code> <code>STRING_LITERAL</code> <code><b>\n</b></code><br>
<code>end</code> <code><b>\n</b></code><br>
</blockquote>