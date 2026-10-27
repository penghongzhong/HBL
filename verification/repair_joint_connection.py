"""Repair only the displayed joint-map connection; preserve theorem hypotheses."""
from pathlib import Path
import subprocess

path = Path('HBL/WeightedJointBackward.lean')
base = 'f224ae2875868dc81145cb02e07d903e8701713c'
original = subprocess.check_output(['git', 'show', f'{base}:{path}'], text=True)
text = original
text = text.replace('set_option autoImplicit false\n', 'set_option autoImplicit false\nset_option backward.isDefEq.respectTransparency false\n', 1)
anchor = '/-- Exact Lipschitz constant of the full repaired centre self-map:'
lemma = '''/-- Translation by the prescribed threshold path preserves the already
proved Lipschitz bound of the actual threshold reconstruction. -/
theorem affineWeightedThresholdMap_lipschitz
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (a0 : ThresholdWeightedPath s0 p) :
    LipschitzWith (Real.toNNReal (‖B‖ / (p - 1)))
      (affineWeightedThresholdMap B s0 p hs0 hp a0) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  simpa only [affineWeightedThresholdMap, dist_add_left] using
    (weightedThresholdMap_lipschitz B s0 p hs0 hp).dist_le_mul q r

'''
assert text.count(anchor) == 1
text = text.replace(anchor, lemma+anchor)
old = '    · rw [hza,hzqstar]\n      rfl\n'
assert text.count(old) == 1
text = text.replace(old, '    · rw [hza,hzqstar]\n')
old_triangle = '''        ≤ ‖Cfb (A q) - Cfb (A r)‖ + ‖CnlMap q-CnlMap r‖ :=
          norm_add_le _ _
'''
new_triangle = '''        ≤ ‖Cfb (A q) - Cfb (A r)‖ + ‖CnlMap q-CnlMap r‖ := by
      have hN : 0 ≤ ‖Cfb (A q) - Cfb (A r)‖ + ‖CnlMap q - CnlMap r‖ := by
        rw [BoundedContinuousFunction.norm_def, BoundedContinuousFunction.norm_def]
        exact add_nonneg dist_nonneg dist_nonneg
      apply (BoundedContinuousFunction.norm_le
        (f := (Cfb (A q) - Cfb (A r)) + (CnlMap q - CnlMap r)) hN).2
      intro t
      change ‖(Cfb (A q) - Cfb (A r)) t + (CnlMap q - CnlMap r) t‖ ≤ _
      exact (norm_add_le ((Cfb (A q) - Cfb (A r)) t)
        ((CnlMap q - CnlMap r) t)).trans
          (add_le_add ((Cfb (A q) - Cfb (A r)).norm_coe_le_norm t)
            ((CnlMap q - CnlMap r).norm_coe_le_norm t))
'''
assert text.count(old_triangle) == 1
text = text.replace(old_triangle, new_triangle)
current = path.read_text()
assert current in [original, text], 'Source changed; reconcile before applying repair'
path.write_text(text)
