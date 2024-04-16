<blockquote><code><b>\n</b></code><br>
<code>funcdef (2)</code> <code>'IsPositive (2)'</code> <code>:: (2)</code> <code>'NumericalPos (2)'</code> <code>→ (2)</code> <code>'Bool (2)'</code> <code><b>\n</b></code><br>
<code>funcdef (3)</code> <code>'IsPositive (3)'</code> <code>'num (3)'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>let (4)</code> <code>'ret_val (4)'</code> <code>as (4)</code> <code>'Numerical (4)'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>do (5)</code> <code>'num (5)'</code> <code>>= (5)</code> <code>NUMERICAL_LITERAL (5)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>on (6)</code> <code>NUMERICAL_LITERAL (6)</code> <code>→ (6)</code> <code>set (6)</code> <code>'ret_val (6)'</code> <code>as (6)</code> <code>NUMERICAL_LITERAL (6)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>on (7)</code> <code>NUMERICAL_LITERAL (7)</code> <code>→ (7)</code> <code>set (7)</code> <code>'ret_val (7)'</code> <code>as (7)</code> <code>NUMERICAL_LITERAL (7)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'return (8)'</code> <code>( (8)</code> <code>'ret_val (8)'</code> <code>) (8)</code> <code><b>\n</b></code><br>
<code>suchthat (9)</code> <code>: (9)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>| (10)</code> <code>'doc (10)'</code> <code>as (10)</code> <code>STRING_LITERAL (10)</code> <code><b>\n</b></code><br>
<code>end (11)</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>typedef (13)</code> <code>'NumericalPos (13)'</code> <code>'a (13)'</code> <code>:: (13)</code> <code>'Numerical (13)'</code> <code>{ (13)</code> <code>'a (13)'</code> <code>>= (13)</code> <code>NUMERICAL_LITERAL (13)</code> <code>} (13)</code> <code><b>\n</b></code><br>
<code>suchthat (14)</code> <code>: (14)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>| (15)</code> <code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'doc (15)'</code> <code>as (15)</code> <code>STRING_LITERAL (15)</code> <code><b>\n</b></code><br>
<code>end (16)</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>typedef (18)</code> <code>'Bool (18)'</code> <code>'a (18)'</code> <code>:: (18)</code> <code>'Integer (18)'</code> <code>{ (18)</code> <code>( (18)</code> <code>'a (18)'</code> <code>= (18)</code> <code>NUMERICAL_LITERAL (18)</code> <code>) (18)</code> <code>∨ (18)</code> <code>( (18)</code> <code>'a (18)'</code> <code>= (18)</code> <code>NUMERICAL_LITERAL (18)</code> <code>) (18)</code> <code>} (18)</code> <code><b>\n</b></code><br>
<code>suchthat (19)</code> <code>: (19)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>| (20)</code> <code>'doc (20)'</code> <code>as (20)</code> <code>STRING_LITERAL (20)</code> <code><b>\n</b></code><br>
<code>end (21)</code> <code><b>\n</b></code><br>
</blockquote>