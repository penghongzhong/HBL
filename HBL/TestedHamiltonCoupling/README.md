# Actual tested Hamilton observation

For the actual half-line operators already defined in `AffineTailOperators.lean`,
construct the continuous linear observation

$$
B(q_f,q_v)=\left(\int_0^R\zeta H_-(rv)\,dr,
 -\int_0^R(rg)H_+(rf)\,dr\right),
\qquad q_f=(rf)',\quad q_v=(rv)'.
$$

The identity is proved for smooth finite-energy profiles. Its assumptions are:
$R\ge0$, $\zeta(0)=\zeta(R)=\zeta'(R)=0$, and a smooth test $g$ vanishing on
$[R,\infty)$. The real channel includes the actual nonlocal Hartree integral.
The construction uses the proved phase Green identity and the proved real
nonlocal Green/Fubini identity. Thus the right-hand side has a continuous
extension to the actual energy pair, and restriction to the closed constrained
centre gives a concrete continuous linear map into $\mathbb R^2$.

This fills the two-channel **tested observation** part of a retained-coupling
construction. The tests remain explicit arguments. Identification with the
normalized moving coordinates, the full three-dimensional Hamilton generator,
its common domain, an invariant splitting and its evolution family remain open.
In particular this construction does not supply a solution to
$D_c^*\lambda=b$, does not prove an exact decoupling and does not restore any
original environment: the strict count remains **9/21**.

`verification/tested_hamilton_coupling_validation.py` builds the historical
foundation normally, then compiles both new sources in a fresh directory with
`--trust=0 -DwarningAsError=true` and audits the full terminal type, definition
bodies and transitive axioms. Foundation build warnings are not a claim of a
strict source re-audit for the whole repository. Each new theorem has its own
source file.

## Fixed normalized coordinates (2026-10-29)

The normalized extension fixes $R=e$, $\zeta=\zeta_+$ and
$g_{\rm ph}=m_-^{-1}\,\mathrm{bump}\,W$ once and for all. It proves smoothness,
$rg_{\rm ph}=\zeta_-$, support and all boundary conditions, and constructs
`normalizedHamiltonCoupling` without arbitrary testing-profile hypotheses.
The coordinate order is scale first and phase second:

$$
B(f,v)=\left(\int_0^e\zeta_+H_-(rv),
-\int_0^e\zeta_-H_+(rf)\right).
$$

For smooth finite-energy outputs $a,b$ satisfying the explicit Hamilton graph
conditions $ra=H_-(rv)$ and $rb=-H_+(rf)$, the final terminal proves

$$
B(f,v)=(\mathrm{scaleCompactTest}(a),\mathrm{phaseCompactTest}(b)).
$$

Thus the observation is identified with the fixed coordinate action on that
smooth graph. These graph conditions do not assert that the graph is closed,
dense or the domain of an evolution generator. No propagation or invariant
splitting follows from this result. New original environments accepted: **0**.
The count remains **9/21**. Run the separate
`verification/normalized_hamilton_coupling_validation.py` for fresh strict
compilation and the full type/axiom audit of this extension.
