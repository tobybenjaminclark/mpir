<blockquote><code><b>\n</b></code><br>
<code>funcdef (2)</code> <code>'test1million (2)'</code> <code>:: (2)</code> <code>'One (2)'</code> <code>→ (2)</code> <code>'Hundred (2)'</code> <code><b>\n</b></code><br>
<code>funcdef (3)</code> <code>'test1million (3)'</code> <code>'a (3)'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'return (4)'</code> <code>( (4)</code> <code>'a (4)'</code> <code>* (4)</code> <code>NUMERICAL_LITERAL (4)</code> <code>) (4)</code> <code><b>\n</b></code><br>
<code>suchthat (5)</code> <code>: (5)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>| (6)</code> <code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'doc (6)'</code> <code>as (6)</code> <code>STRING_LITERAL (6)</code> <code><b>\n</b></code><br>
<code>end (7)</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>funcdef (9)</code> <code>'make_one (9)'</code> <code>:: (9)</code> <code>'Numerical (9)'</code> <code>→ (9)</code> <code>'One (9)'</code> <code><b>\n</b></code><br>
<code>funcdef (10)</code> <code>'make_one (10)'</code> <code>'num (10)'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>let (11)</code> <code>'return_val (11)'</code> <code>as (11)</code> <code>'One (11)'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>let (12)</code> <code>'return_val_test (12)'</code> <code>as (12)</code> <code>'Numerical (12)'</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>trycast (14)</code> <code>'num (14)'</code> <code>into (14)</code> <code>'return_val (14)'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>on (15)</code> <code>NUMERICAL_LITERAL (15)</code> <code>→ (15)</code> <code>set (15)</code> <code>'return_val_test (15)'</code> <code>as (15)</code> <code>NUMERICAL_LITERAL (15)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>on (16)</code> <code>NUMERICAL_LITERAL (16)</code> <code>→ (16)</code> <code>set (16)</code> <code>'return_val_test (16)'</code> <code>as (16)</code> <code>NUMERICAL_LITERAL (16)</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'return (18)'</code> <code>( (18)</code> <code>'return_val_test (18)'</code> <code>) (18)</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>suchthat (20)</code> <code>: (20)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>| (21)</code> <code>'doc (21)'</code> <code>as (21)</code> <code>STRING_LITERAL (21)</code> <code><b>\n</b></code><br>
<code>end (22)</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>funcdef (24)</code> <code>'one (24)'</code> <code>:: (24)</code> <code>'Numerical (24)'</code> <code>→ (24)</code> <code>'One (24)'</code> <code><b>\n</b></code><br>
<code>funcdef (25)</code> <code>'one (25)'</code> <code>'num (25)'</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'return (26)'</code> <code>( (26)</code> <code>NUMERICAL_LITERAL (26)</code> <code>) (26)</code> <code><b>\n</b></code><br>
<code>suchthat (27)</code> <code>: (27)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>| (28)</code> <code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>'doc (28)'</code> <code>as (28)</code> <code>STRING_LITERAL (28)</code> <code><b>\n</b></code><br>
<code>end (29)</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>typedef (31)</code> <code>'One (31)'</code> <code>'a (31)'</code> <code>:: (31)</code> <code>'Integer (31)'</code> <code>{ (31)</code> <code>( (31)</code> <code>'a (31)'</code> <code>= (31)</code> <code>NUMERICAL_LITERAL (31)</code> <code>) (31)</code> <code>∨ (31)</code> <code>( (31)</code> <code>'a (31)'</code> <code>= (31)</code> <code>NUMERICAL_LITERAL (31)</code> <code>) (31)</code> <code>} (31)</code> <code><b>\n</b></code><br>
<code>suchthat (32)</code> <code>: (32)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>| (33)</code> <code>'doc (33)'</code> <code>as (33)</code> <code>STRING_LITERAL (33)</code> <code><b>\n</b></code><br>
<code>end (34)</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code>typedef (36)</code> <code>'Hundred (36)'</code> <code>'a (36)'</code> <code>:: (36)</code> <code>'Integer (36)'</code> <code>{ (36)</code> <code>'a (36)'</code> <code>< (36)</code> <code>NUMERICAL_LITERAL (36)</code> <code>} (36)</code> <code><b>\n</b></code><br>
<code>suchthat (37)</code> <code>: (37)</code> <code><b>\n</b></code><br>
<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code><code>| (38)</code> <code>'doc (38)'</code> <code>as (38)</code> <code>STRING_LITERAL (38)</code> <code><b>\n</b></code><br>
<code>end (39)</code> <code><b>\n</b></code><br>
<code><b>\n</b></code><br>
<code><b>\n</b></code><br>
</blockquote>