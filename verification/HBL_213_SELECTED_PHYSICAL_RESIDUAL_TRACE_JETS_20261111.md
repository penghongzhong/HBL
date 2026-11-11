# HBL §2.13 — exact source-produced interface jets of the selected *full* Hartree PDE

11 November 2026. **Paper-only trace identity, not an accepted new Lean theorem. Retained original acceptance 11/13.** The purpose is to decide whether the actual two-speed-selected four-region field needs a C³ interface patch before introducing any extra shell, rather than treating curvature/third jets as independent small variables.

## 1. Same globally evaluated nonlinear operator and moving C¹ data

Fix one of the three genuine physical interfaces \(r=L(s)>0\), and let \(W_\pm(s,r)\) denote the one-sided restrictions of the **same global radial physical field**. Assume enough one-sided \(C^1_sC^3_r\) and mixed differentiability for the displayed traces, and at the moving interface
\[
 [W]=[W_r]=0,\qquad [f]:=f(s,L(s)+)-f(s,L(s)-).
 \tag{JT1}
\]
The full inverse-square quartic Hartree nonlinearity is computed on the *entire* field, not separately on artificial truncated pieces:
\[
 \mathcal N_H(W)=\kappa_H (|\cdot|^{-2}*|W|^4)|W|^2W,\quad
 \mathscr R_W=iW_s+W_{rr}+\frac2rW_r+\mathcal N_H(W).
 \tag{JT2}
\]
At the interface assume the true convolution potential and its first radial derivative are continuous; this follows for the smooth, sufficiently decaying global packets for which their convolution and first derivative are well-defined. Since \(W,W_r\) match, both \([\mathcal N_H(W)]=0\) and \([\partial_r\mathcal N_H(W)]=0\). These continuity conditions concern the *actual globally evaluated convolution*; they are not an independently assumed small source envelope.

Differentiating the moving matching traces (JT1) gives the two exact chain rules
\[
 [W_s]=0,\qquad [W_{sr}]=-L'[W_{rr}].
 \tag{JT3}
\]
Introduce the actual one-sided curvature and third-jet mismatch
\[
 d_2=W_{rr}(L-)-W_{rr}(L+)=-[W_{rr}],\qquad
 d_3=W_{rrr}(L-)-W_{rrr}(L+)=-[W_{rrr}].
 \tag{JT4}
\]

## 2. Source/jet formulas (no independent jet assumptions)

Taking the jumps of (JT2), then its radial derivative, and using (JT3) yields
\[
 \boxed{d_2=-[\mathscr R_W]},\qquad
 \boxed{d_3=-[\partial_r\mathscr R_W]
                  +(iL'-2/L)d_2.}
 \tag{JT5}
\]
Indeed,
\[
 [\mathscr R_W]=[W_{rr}]=-d_2,\qquad
 [\partial_r\mathscr R_W]
 =i[W_{sr}]+[W_{rrr}]+\frac2L[W_{rr}]
 =-d_3-\Bigl(\frac2L-iL'\Bigr)d_2.
\]
These identities concern the **true four-region PDE residual**, including all nonlocal cross interactions. If the two adjoining restrictions are already exact classical solutions of the same full physical PDE on neighborhoods of the interface, \(\mathscr R_W=0\) there and thus \(d_2=d_3=0\); no Hermite curvature repair is needed at that interface. Conversely, a C¹ match and the two-real-speed selector *alone* do not imply the two equalities \([\mathscr R_W]=[\partial_r\mathscr R_W]=0\).

If the one-sided residual traces are differentiable in time along the moving interface, differentiating (JT5) *as total traces* gives
\[
 \boxed{d_2'=-[\partial_s\mathscr R_W]
                 -L'[\partial_r\mathscr R_W],}
 \tag{JT6}
\]
and, when \(L\in C^2\) and the displayed higher traces exist,
\[
 \boxed{\begin{aligned}
 d_3'={}&-[\partial_s\partial_r\mathscr R_W]
           -L'[\partial_r^2\mathscr R_W]\\
       &+(iL''+2L'/L^2)d_2+(iL'-2/L)d_2'.
 \end{aligned}}
 \tag{JT7}
\]
Thus merely inserting (JT5) into a bound for \(\mathscr R_W\) is *circular*: (JT5) identifies the missing producers, but does not establish decay of the residual or its time derivative. The productive use is to compute the **unrepaired one-sided physical residual traces directly from each explicit original PDE piece**, with the unique selected real speeds and the full Hartree convolution, and then show whether their jumps vanish or are small.

## 3. Exact result of the original Hermite repair

If a nonzero source jump remains, the existing physical-shell construction
\[
 P=h^2d_2\phi_2((r-L)/h)+h^3d_3\phi_3((r-L)/h),\quad L<r<L+h,
 \tag{JT8}
\]
extended by zero, has \([P]=[P_r]=0\), \([P_{rr}]=d_2\), \([P_{rrr}]=d_3\), and, from differentiated moving C¹ matching, \([P_{sr}]=-L'd_2\). Therefore the complete **repaired field** \(U=W+P\) satisfies
\[
 [U]=[U_r]=[U_{rr}]=[U_{rrr}]=[U_s]=[U_{sr}]=0.
 \tag{JT9}
\]
The nonlinear potential of \(U\), including global feedback from the shell, still has continuous value and radial derivative at the interface. Consequently, in its full physical PDE residual,
\[
 \boxed{[\mathscr R_U]=[\partial_r\mathscr R_U]=0.}
 \tag{JT10}
\]
This is exact interface **regularity**; it is not \(\|\mathscr R_U\|_X\lesssim s^{-9/4}\), nor a bound on \(\partial_s\mathscr R_U\) or parameter differences. The nonlocal feedback need not vanish at the endpoints merely because \(P\) and \(P_r\) do: its *traces match*, rather than being zero. Source-norm gain must be proved on the assembled \(U\), not by separately assigning strong norms to the moving distributional terms of \(W\) and \(P\).

## 4. Shortest productive branch and formal boundary

1. At each of the three **actual** moving interfaces, evaluate \([\mathscr R_W]\) and \([\partial_r\mathscr R_W]\) from the explicit selected four-piece PDE and the same genuine nonlocal source; preserve the outgoing mismatch rather than setting it to zero by hand.
2. Where both traces vanish, use (JT5) to remove an unnecessary C³ patch. Where nonzero, compute actual \(d_2,d_3\) by (JT5), use (JT6)–(JT7) for moving budgets, and control the full post-repair residual, including nonlocal feedback and the remaining regular terms.
3. Establish genuine positive time gain and two-parameter Lipschitz in the **original strong source topology**, then finite-layer recursion and a PDE-derived II-type blowup law. Do not turn (JT10) into a residual decay estimate.

The accepted nonlinear PDE telescoping theorem in [CI 42958494409](https://github.com/penghongzhong/HBL/actions/runs/42958494409) is only an algebraic identity and does not prove these trace estimates. All of (JT1)–(JT10) are paper derivations: **no new Lean compilation or axiom audit is claimed**. Original revised §2.13 and the final theorem remain open; verified count **11/13 (84.62%)**.
