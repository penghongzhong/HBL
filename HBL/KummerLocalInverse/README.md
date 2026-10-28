# Actual local Kummer bounded linear right inverse

For every fixed real `mu`, `theta` and positive physical radius `z`, the terminal
`exists_actual_localKummer_bounded_rightInverse` constructs a positive annulus
`I = [z-d,z+d]`, with `d = eps/2 > 0` and `z-d > 0`, and a complex continuous
linear map

\[
 T:C(I;\mathbb C)\longrightarrow C(I;\mathbb C^2),\qquad TF=(u,u').
\]

The actual normalized Picard–Lindelöf basis supplies `eps`, a bound `C > 0`,
and a nonvanishing Wronskian. The map satisfies

\[
 \|T\|\le4dC^3=2\varepsilon C^3,\qquad
 \|TF-TG\|_{C(I;\mathbb C^2)}\le4dC^3\|F-G\|_{C(I;\mathbb C)}.
\]

The output norm uses the maximum product norm. The underlying pointwise
estimate also bounds `|u(r)| + |u'(r)|` by the same displayed constant times
an arbitrary uniform source bound. The value and derivative are continuous
on the closed annulus and have genuine first/second radial derivatives there.
For every continuous source on `I`, the exact physical equation is

\[
 u''(r)+\left(\frac2r+\frac{ir}{2}\right)u'(r)
 +\left(\theta+i\left(\frac14-\mu\right)\right)u(r)=F(r).
\]

In shifted coordinate `t=r-z`, the variation-of-parameters coefficients are

\[
 A_F(t)=\int_t^d\frac{\psi(s)F(z+s)}{W(s)}\,ds,\qquad
 B_F(t)=\int_{-d}^t\frac{\phi(s)F(z+s)}{W(s)}\,ds.
\]

Thus `A_F(d)=0`, `B_F(-d)=0`, and the actual output obeys

\[
 u(z+d)\psi'(d)-u'(z+d)\psi(d)=0,\qquad
 \phi(-d)u'(z-d)-\phi'(-d)u(z-d)=0.
\]

Continuous sources are defined on the compact annulus itself; a continuous
clamping extension is used internally, with its exact restriction and norm
bound proved. No global physical fundamental pair or assumed inverse is used.
The source-independent pair and its bounds are constructed from the existing
actual physical IVPs. The terminal has no fundamental-pair hypothesis.

All 25 new theorems occur in separate files. The other six source files contain
definitions. All 31 source files lie on the terminal's import chain.

Run `python verification/kummer_local_inverse_validation.py` in the pinned Lean
environment. It builds the terminal and its dependencies, strictly checks each
source with `--trust=0 -DwarningAsError=true` into an isolated temporary build
directory in dependency order, and audits complete types and transitive axioms
against those fresh artifacts. It checks import closure and verifies that sources
and compiled artifacts stay unchanged during validation. Full output is retained
in reproducible gzip with hashes.

Scope: the annulus is a constructed neighborhood of one positive radius at
fixed parameters. A prescribed larger matching annulus, common annuli and
uniform constants over compact parameter families, and parameter derivatives
remain open. Original manuscript acceptance stays **9/21**;
`prop:one-layer-stage3` and the main PDE theorem remain **OPEN**.
