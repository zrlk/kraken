import Kraken.X64.Examples.Sbr.SessionBin.MultiReach

/-!
# More than one element: an element's memory, split into its own and the shared part

`elemAt_split`: in an environment that shares the caller's tables and state (`EnvShares`),
the element's memory (`ElemAt … ⋆ InitGap che`) is its own allocation (`ElemOwn`) and the
shared part: the cell `ac->fdsp`, the `float_dsp` slots it points to and `SharedData`. The
regroupings are stated on abstract predicates first (`fn_perm`, `elem_perm`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init
open Std.ExtHashMap (sep_assoc sep_comm)

namespace Kraken.Examples.Sbr.SessionBin

/-! ## Regroupings on abstract predicates -/

theorem fn_tail_perm (C1 C2 F1 F2 F3 T : Mem 64 → Prop) :
    F1 ⋆ (F2 ⋆ (F3 ⋆ (C1 ⋆ (C2 ⋆ T)))) = C1 ⋆ (C2 ⋆ (F1 ⋆ (F2 ⋆ (F3 ⋆ T)))) := by
  ac_rfl

/-- `FnW`'s shape: eight cells, the three `float_dsp` slots, two contexts, the tables. -/
theorem fn_perm (A1 A2 A3 A4 A5 A6 A7 A8 F1 F2 F3 C1 C2 T : Mem 64 → Prop) :
    A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆ (A8 ⋆ (F1 ⋆ (F2 ⋆ (F3 ⋆ (C1 ⋆ (C2 ⋆ T))))))))))))
    = (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆ (A8 ⋆ (C1 ⋆ C2)))))))))
      ⋆ ((F1 ⋆ (F2 ⋆ F3)) ⋆ T) := by
  simp only [sep_assoc]
  rw [fn_tail_perm C1 C2 F1 F2 F3 T]

/-- `ElemAt … ⋆ InitGap`'s shape, with `FnW` split, regrouped as `ElemOwn` and the rest. -/
theorem elem_perm (A B C D O F T P X K Q G : Mem 64 → Prop) :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ ((O ⋆ (F ⋆ (T ⋆ (P ⋆ X)))) ⋆ (K ⋆ Q)))))) ⋆ G
    = (A ⋆ (B ⋆ (C ⋆ (D ⋆ (O ⋆ G))))) ⋆ (K ⋆ (F ⋆ (T ⋆ (P ⋆ (X ⋆ Q))))) := by
  simp only [sep_assoc]
  have e : O ⋆ (F ⋆ (T ⋆ (P ⋆ (X ⋆ (K ⋆ (Q ⋆ G))))))
      = O ⋆ (G ⋆ (K ⋆ (F ⋆ (T ⋆ (P ⋆ (X ⋆ Q)))))) := by ac_rfl
  rw [e]

/-! ## The element's cells depend on `che` only -/

theorem sbrA_tAt_ac (che ac : BitVec 64) : sbrA (tAt che ac) = sbrA (tAt che 0#64) := by
  simp [sbrA, tAt, arg1]

theorem psRest_tAt (x : Args) (che ac : BitVec 64) :
    PsRest x (tAt che ac) = PsRest x (tAt che 0#64) := by
  simp only [PsRest, sbrA_tAt_ac che ac]

theorem arrW_tAt (che ac : BitVec 64) : ArrW (tAt che ac) = ArrW (tAt che 0#64) := by
  simp only [ArrW, sbrA_tAt_ac che ac]

theorem dspW_tAt (e : Env) (che ac : BitVec 64) : DspW e (tAt che ac) = DspW e (tAt che 0#64) := by
  simp only [DspW, sbrA_tAt_ac che ac]

theorem fnOwn_tAt (e : Env) (x : Args) (che ac : BitVec 64) :
    FnOwn e x (tAt che ac) = FnOwn e x (tAt che 0#64) := by
  simp only [FnOwn, sbrA_tAt_ac che ac]

/-! ## The splits -/

/-- `FnW` is the element's own cells and contexts, the `float_dsp` slots and the tables. -/
theorem fnW_split (e : Env) (x : Args) (t : MachineData) :
    FnW e x t = FnOwn e x t ⋆ (FdspW e x.fdsp ⋆ (e.TxTab ⋆ (e.PsTab ⋆ e.Ext))) := by
  unfold FnW FnOwn FdspW
  exact fn_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The element's memory, split**: its own allocation, and the cell `ac->fdsp`, the
`float_dsp` slots and the shared data. -/
theorem elemAt_split [CodeEnv] {S : Setup} {e : Env} (hsh : EnvShares S e) (σ : SV)
    (che ac : BitVec 64) :
    (ElemAt e S.vs S.vp σ che ac ⋆ InitGap che)
      = ElemOwn e σ che
        ⋆ (c8 (ac + 0x2550#64) σ.1.fdsp ⋆ (FdspW S.env σ.1.fdsp ⋆ SharedData S)) := by
  obtain ⟨h1, h2, h3, hf1, hf2, hf3⟩ := hsh
  have h4 : FdspW e = FdspW S.env := by
    funext a; unfold FdspW; rw [hf1, hf2, hf3]
  simp only [ElemAt, ElemOwn]
  rw [fnW_split, psRest_tAt σ.1 che ac, arrW_tAt che ac, dspW_tAt e che ac, fnOwn_tAt e σ.1 che ac,
    sbrA_tAt_ac che ac, h1, h2, h3, h4]
  exact elem_perm _ _ _ _ _ _ _ _ _ _ _ _

/-- The element's own part does not read `ac->fdsp`'s value. -/
theorem elemOwn_setF (e : Env) (σ : SV) (che f : BitVec 64) :
    ElemOwn e (setF f σ) che = ElemOwn e σ che := rfl

end Kraken.Examples.Sbr.SessionBin
