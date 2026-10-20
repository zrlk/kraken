import WeakCore.TermOwnG0W
import WeakCore.TermPlantWin

/-!
# TermGbLp: the planted count bound of a plant's certificate run (G-b, phase 1)

A promise `promise cP i a0 v0 w` plants the labels `Lp` at the counts `max ini NpZ` (`plantE`).
Fix a planted own label `a`. Along the promise's certificate run before a `publish` naming `a`
(`SoloNP`), the G-0 window `G0WinW` keeps `vWr ≤ wt < cP.mem.size`. So every unit that the run's
count adds at `a` was written at an index below the plant's memory size (`IniHeld` with `WitP`), i.e.
by a promise outstanding at the plant at that unit. The count therefore stays inside the held prefix,
`≤ NpZ` (`iniLp_of`). The owner's invariant at the end of the run bounds the count by the slot count
and keeps it at a zero-width uninhabited buffer (`bufCap_of`). A non-buffer cell's count is the
explicit hypothesis `CapNAt` (at that cell only).

`TermOwnG0Defs.PostPubFreeze` is superseded: the count after the `publish` is frozen by the publish-chain
machinery (`IniLoc` at `{a}`), not by a run hypothesis.
-/

namespace TermGbLp

open CoreLang CoreTerm TermRun TermSound TermMem TermStep TermTyped TermOwnG0Defs TermOwnG0W
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (G-b, explicit hypothesis, per cell) A planted own cell that is not a buffer (`slotCnt = 0`) keeps its count
along the run: the footprint does not record that `rini` is raised only at buffers (`RINIARR_SPEC`). -/
def CapNAt (E0 E : TEnv) (l : AllocLabel) : Prop :=
  ∀ c, E0.sto l = some c → (¬ ∃ N e, c.ty = .array (.lit N) e) → E.ini l ≤ E0.ini l

/-- An own cell's words at the real count: a buffer's real count is at most its slot count, and a
zero-width element type with a counted slot is inhabited. -/
theorem bufCap_of {E : TEnv} {mem : Memory} {pairs : List Ts} {vs : VState} {P : List Ts} {l : AllocLabel}
    {c : Cell} {N : Nat} {e : Ty} (hok : OwnOKPF E mem pairs vs P) (hc : E.sto l = some c)
    (ho : c.owner = some E.tid) (hT : c.ty = .array (.lit N) e) :
    ∃ us, accs e = some us ∧ E.rc l ≤ N ∧ (nWords us = 0 → 0 < E.rc l → InhZ E.prog e) := by
  obtain ⟨vals, hC, -⟩ := hok l c hc ho
  rcases hC with ⟨hw, -⟩ | ⟨N1, e1, us, hT1, hus, hle, -, hv⟩
  · rw [hT, TermCut.wc_array] at hw; cases hw
  rw [hT] at hT1
  simp only [Ty.array.injEq, Idx.lit.injEq] at hT1
  obtain ⟨rfl, rfl⟩ := hT1
  refine ⟨us, hus, hle, fun h0 hpos => ?_⟩
  have h := hv 0 hpos
  rw [h0, List.take_zero] at h
  exact ⟨[], ⟨TermPlantWin.VR_nil_congr e (CE E.unsee) (CE ({ prog := E.prog } : TEnv).unsee) _ _ rfl rfl rfl h.1, h.2⟩, rfl⟩

/-- **(G-b) `CapNAt` from the run's held counts** (the `EFoot.riniArr`, carried by `IniHeld_foot`): at a
start non-buffer cell the real count has not risen, so the count stays at most `max ini rini` of the
start, i.e. its start count. -/
theorem capNAt_of {H : AllocLabel → Nat → Ts → Prop} {E0 E : TEnv} {v : Nat} (hrl : ∀ l, E0.rini l ≤ E0.ini l)
    (hIH : IniHeld H E0 E v) (l : AllocLabel) : CapNAt E0 E l := by
  intro c hc hnb
  obtain ⟨-, -, hmx, hna⟩ := hIH hrl
  have h2 := hna l c hc (fun ⟨N, e, _, hT, _⟩ => hnb ⟨N, e, hT⟩)
  exact Nat.le_trans (hmx l c hc) (Nat.max_le.2 ⟨Nat.le_refl _, Nat.le_trans h2 (hrl l)⟩)

/-- **(G-b) The planted count bound, before the root's publish.** -/
theorem iniLp_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {cP c2 : Cfg} {i : Nat} {thP th2 : TTh}
    {a0 : Address} {v0 : WeakMem.Val} {w : Ts} {r : AllocLabel} {E0 E2 : TEnv} {Lp : AllocLabel → Prop}
    {g : G} {s2 : St}
    {wt : Ts} (hw : wt < cP.mem.size) (hrl : ∀ l, E0.rini l ≤ E0.ini l)
    (hG0 : G0WinW p k arch cP i a0 v0 w r wt) (hNP : SoloNP p k arch i r (promise cP i a0 v0 w) c2)
    (hc2 : Certified p k arch c2 i) (hth2 : c2.ths[i]? = some th2)
    (hIH : IniHeld (WitP cP.mem thP.promises) E0 E2 th2.vs.vWr) (hext : Ext E0 E2) (hmi : MemInv g E2 s2)
    {l : AllocLabel} {c : Cell} (hl : Lp l) (hc : E0.sto l = some c) (ho : c.owner = some E0.tid)
    (hcap : CapNAt E0 E2 l) :
    E2.ini l ≤ (plantE E0 (stOf cP.mem cP.pairs thP) Lp).ini l := by
  rw [plantE_ini_in hl]
  by_cases hle : E2.ini l ≤ E0.ini l
  · exact Nat.le_trans hle (Nat.le_max_left _ _)
  obtain ⟨hrl2, hu, hmx, -⟩ := hIH hrl
  obtain ⟨N, e, hT⟩ : ∃ N e, c.ty = .array (.lit N) e :=
    Classical.byContradiction fun hb => hle (hcap c hc hb)
  have hc2s : E2.sto l = some c := hext.2.2.2.2.1 l c hc
  have ho2 : c.owner = some E2.tid := by rw [hext.2.2.2.1]; exact ho
  obtain ⟨us, hus, hN, hZ⟩ := bufCap_of hmi.2.1 hc2s ho2 hT
  have hrc : E2.rc l = E2.ini l := by
    have h1 := hmx l c hc
    have h2 := hrl2 l
    unfold TEnv.rc
    rcases Nat.le_total (E0.ini l) (E2.rini l) with h | h
    · rw [Nat.max_eq_right h] at h1; exact Nat.min_eq_left h1
    · rw [Nat.max_eq_left h] at h1; exact absurd h1 hle
  rw [hrc] at hN hZ
  have hNa : E2.ini l ≤ N := hN
  by_cases hE : EmptyZ E0 l
  · exfalso
    obtain ⟨c1, N1, e1, us1, hc1, hT1, hus1, h01, hinh⟩ := hE
    rw [hc] at hc1; cases hc1
    rw [hT] at hT1
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT1
    obtain ⟨rfl, rfl⟩ := hT1
    rw [hus] at hus1; cases hus1
    have := hZ h01 (Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_of_not_le hle))
    rw [hext.2.2.1] at this
    exact hinh this
  have hv : th2.vs.vWr ≤ wt := hG0 c2 th2 hNP hc2 hth2
  have hpre : PrefixHeld E0 (stOf cP.mem cP.pairs thP) l c (E2.ini l) := by
    intro N' e' us' hT' hus' o ho'
    rw [hT] at hT'
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
    obtain ⟨rfl, rfl⟩ := hT'
    rw [hus] at hus'
    cases hus'
    by_cases hlt : o < E0.ini l * nWords us
    · refine Or.inl fun N2 e2 us2 hT2 hus2 => ?_
      rw [hT] at hT2
      simp only [Ty.array.injEq, Idx.lit.injEq] at hT2
      obtain ⟨rfl, rfl⟩ := hT2
      rw [hus] at hus2
      cases hus2
      exact hlt
    · obtain ⟨τ, hτ, hW⟩ := hu l c hc ho N e us hT hus o ho' hlt
      rcases hW with h | ⟨hτP, m, hm, hloc⟩
      · exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans hτ hv) hw) (Nat.not_lt.2 h)
      · exact Or.inr ⟨τ, hτP, m, hm, hloc⟩
  rw [NpZ_of_not hE]
  exact Nat.le_trans (le_Np hc hT hNa hpre) (Nat.le_max_right _ _)

end TermGbLp

#print axioms TermGbLp.bufCap_of
#print axioms TermGbLp.iniLp_of
#print axioms TermGbLp.capNAt_of
