# HBL §2.13: correct the conditional inner C² patch time geometry (10 November 2026)

**Original revised acceptance: 11/13.** This is a rigorous scalar consistency check, **not** a real Hartree orbit, a Lean certificate, or a proven time-positive PDE residual. It repairs the interpretation of the illustrative \(L(s)\ge c\sqrt{s}\) calculation in the current manuscript and ledger; no previously audited theorem changes.

## 1. The genuine modulation equations prohibit the illustrative half-power radius

The actual retained slow overlap is \(L(s)=\ell(s)^{-1/16}\). If an eventual physical solution produces the projected real modulation identities
\[
 q_s=4\mu,\qquad \ell_s/\ell=-\frac{1+4\mu}{2q},
 \qquad q(s_0)>0,\quad \ell(s_0)>0,\quad
 9/16<m\le\mu(s)\le M<\infty ,
\]
then
\[
 q_0+4m(s-s_0)\le q(s)\le q_0+4M(s-s_0)
\]
and, by exact logarithmic differentiation,
\[
 \ell(s)=\ell_0\sqrt{\frac{q_0}{q(s)}}
 \exp\left(-\frac12\int_{s_0}^s\frac{dv}{q(v)}\right).
\]
Thus for \(s\) sufficiently large,
\[
 C_-s^{-\beta_{\max}}\le \ell(s)\le
 C_+s^{-\beta_{\min}},\qquad
 \beta_{\min}=\frac12+\frac{1}{8M},\quad
 \beta_{\max}=\frac12+\frac{1}{8m}<\frac{13}{18}.
\]
Taking the negative sixteenth power gives the **actual conditional geometry**
\[
 \boxed{\;
 c\,s^{\gamma_{\min}}\le L(s)\le C\,s^{\gamma_{\max}},
 \quad
 \gamma_{\min}=\frac1{32}+\frac1{128M},\quad
 \gamma_{\max}=\frac1{32}+\frac1{128m}<\frac{13}{288}<\frac12 .
 \;}
 \tag{G}
\]
Therefore the previous illustrative assumption \(L(s)\ge c\sqrt{s}\) is **incompatible**, for all sufficiently large \(s\), with the very modulation trapping regime needed for the original HBL II-type main theorem. It must **not** be used as a possible original-orbit estimate. This is a conditional no-go for that proof shortcut, not an impossibility theorem for Hartree blowup.

## 2. Recompute the exact sufficient source exponent

The original *local patch only* estimate was obtained under explicit uniform frozen-Kummer and source-shell coefficient bounds and \(a(s)\ge L(s)^3\):
\[
 {\cal J}_{\rm patch}(s)\lesssim
 L(s)^{-5/2}N(s)
 +L(s)^{-9/2}\bigl(N(s)+|\delta(s)|\,|u_0(s,L(s)/a(s))|\bigr),
 \tag{P}
\]
where \(N(s)=\|F_+(s)\|_{2,7/4}+\|F_-(s)\|_{2,7/4}\) is the literal two-channel weighted Fredholm source norm. No decay of \(N,\delta,u_0\), or the original coefficients is postulated by (P).

Under the **conditional** trapping above, the only guaranteed useful lower rate for \(L\) is \(\gamma_{\min}\); hence
\[
 {\cal J}_{\rm patch}(s)\lesssim
 s^{-5\gamma_{\min}/2}N(s)+
 s^{-9\gamma_{\min}/2}\bigl(N(s)+|\delta(s)|\,|u_0(s,L/a)|\bigr).
 \tag{P'}
\]
For this *specific upper-bound method*, the first term achieves target \(O(s^{-p})\) if the **separately proved** source bound satisfies
\[
 \boxed{N(s)=O\!\left(s^{-[p-(5/2)\gamma_{\min}]}\right).}
 \tag{T}
\]
The second term has its own independent sufficiency condition
\[
 N(s)+|\delta(s)|\,|u_0(s,L/a)|
 =O\!\left(s^{-[p-(9/2)\gamma_{\min}]}\right).
\]
Since \(\gamma_{\min}<13/288\), even the *most favorable allowable* leading-term source exponents in this route must be stricter than
\[
 \begin{array}{c|c}
  p& p-\frac52\frac{13}{288}\\\hline
  15/8&1015/576\;(=1.76215\ldots)\\
  17/8+\eta&1159/576+\eta\;(=2.01215\ldots+\eta)\\
  9/4&1231/576\;(=2.13715\ldots)
 \end{array}
\]
not the earlier \(5/8,\ 7/8+\eta,\ 1\) obtained with the incompatible \(L\sim s^{1/2}\) illustration. More precisely, the actual sufficient exponents depend on **the unknown upper trap \(M\)** through \(\gamma_{\min}\), and are *larger* than these tabulated lower thresholds. These are requirements of this **one inequality (P)** only, not necessary conditions for the true full Hartree PDE residual, which might have cancellations or a genuine projected inverse gain.

## 3. Strict proof and CI boundary

The historical full four-piece PDE telescope is strictly compiled in CI **42536552509**; it is only an identity. The exact inner/spectral C² *pointwise same-source shell budget* was strictly compiled and axiom-audited in CI **42854633900**, job **129964186672**, artifact **13782747879**, with pinned Lean 4.35.0-rc3 / Mathlib \`a98628e16c11f5167f16124105ddce53efa9bfe5\`, \`--trust=0\`, \`warningAsError\`, and only \`propext\`, \`Classical.choice\`, \`Quot.sound\`. Neither strict theorem asserts the modulation trapping hypothesis, the \(N(s)\) bound, the full moving source's time gain, the projected Hartree inverse, or a real PDE orbit.

**Next load-bearing step:** reject \(L\ge c\sqrt{s}\) as a proof input; either derive (T) and the spectral term from the **same actual Hartree source and modulation equations**, or use a quantitatively superior flat-overlap cancellation / projected-inverse route that bounds the **complete nonlinear residual**. Do not increase the original acceptance counter without the original §2.13 theorem type and its dedicated strict CI. **11/13 remains.**
