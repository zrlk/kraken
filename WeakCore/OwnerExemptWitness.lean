import WeakCore.GenLayer
/-! MemInvB-level non-vacuity witness for the owner exemption.
State: own `int` cell 7, unseen frontier 1, placeholder t0 + init t1, coh 1, vWr 1; the
address word `pw` (view 0) is ♭-typed only through the `.loc` arm's owner exemption (flag `False ∨ IniAt rc`),
and `locLoadIB` (the owner branch of `tstepM_loadCellLocB`) applies at `MemInvB`. -/
namespace OwnerExemptWitness
open CoreLang WeakMem TermSound TermRun TermClose TermMem TermStep TermSound.Flat TermStep.Flat TermMem.Flat TermTear.Flat

def cO : Cell := ⟨.int, some 0⟩
def E : TEnv := { sto := fun l => if l = 7 then some cO else none, pfr := fun l => if l = 7 then some 1 else none }
def m0 : Msg := ⟨⟨7, 0⟩, .undef, 0⟩
def m1 : Msg := ⟨⟨7, 0⟩, .num 5, 0⟩
def mem0 : Memory := #[m0, m1]
def vs1 : VState := { (default : VState) with coh := fun a => if a = ⟨7, 0⟩ then 1 else 0, vWr := 1 }
def s1 : St := { mem := mem0, pairs := [], vs := vs1, promises := [], nalloc := 0, undefs := 0 }
def g0 : G := { p := [], k := default, arch := .arm, n := 1, i := 0, lbase := 8 }
def pw : Word := ⟨.loc ⟨7, 0⟩ 0, 0, 0⟩

theorem sto_E {l : AllocLabel} {c : Cell} (h : E.sto l = some c) : l = 7 ∧ c = cO := by
  simp only [E] at h; split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · cases h

theorem mem_E {t : Nat} {m : Msg} (h : mem0[t]? = some m) : (t = 0 ∧ m = m0) ∨ (t = 1 ∧ m = m1) := by
  match t, h with
  | 0, h => exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  | 1, h => exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
  | n + 2, h => simp [mem0] at h

theorem seg_int {b : Nat} {S : Ty} (h : SegOf .int b S) : b = 0 ∧ S = .int := by
  rcases h with ⟨h1, h2, -⟩ | ⟨N, us, j, h1, -⟩
  · exact ⟨h1, h2⟩
  · cases h1

theorem accs_int : accs Ty.int = some [.one] := rfl

theorem valOf_num (η : TEnv) (w : Word) (n : Nat) (hw : w.val = .num n) : ValOfSB η .int [w] := by
  refine ⟨⟨?_, trivial⟩, fun us h => ?_⟩
  · show (VRF False) (fun _ => 0) (CE η.unsee) .int (shp .int) [w]
    simp only [VRF, VRb2]; exact ⟨n, by simp [hw]⟩
  · rw [accs_int] at h; cases h; rfl

theorem wordOK_m1 (η : TEnv) : WordOKB η .int 0 (mw m1) :=
  ⟨0, .int, [mw m1], 0, mw m1, Or.inl ⟨rfl, rfl, by decide⟩, valOf_num η _ 5 rfl, rfl,
    ⟨rfl, fun _ _ _ => Nat.le_refl _⟩, rfl⟩

theorem twoAt_int {o : Nat} : ¬ TwoAtT Ty.int o := by
  rintro ⟨b, S, us, o', hS, hus, htw, -⟩
  obtain ⟨-, rfl⟩ := seg_int hS
  rw [accs_int] at hus; cases hus
  obtain ⟨i, hi, -⟩ := htw
  match i, hi with
  | 0, hi => cases hi
  | n + 1, hi => simp at hi

/-- (M) The witness state satisfies W's full `MemInv`, with the cell owned by the reader. -/
theorem memInvB : MemInvB g0 E s1 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ⟨?_, ?_⟩⟩, ?_, ?_⟩
  -- MemOKP
  · intro t m c _ hm hc
    rcases mem_E hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨-, rfl⟩ := sto_E hc; exact Or.inr (wordOK_m1 E)
  · intro t _ _ _ ht; cases ht
  · intro t ht; cases ht
  -- OwnOKPF: the own cell is at its latest message m1 (coherence 1)
  · intro l c hc _
    obtain ⟨rfl, rfl⟩ := sto_E hc
    refine ⟨[mw m1], Or.inl ⟨rfl, (valOf_num E _ 5 rfl).1⟩, fun o v hv => ?_, fun _ => ?_⟩
    · match o, hv with
      | 0, hv =>
        cases hv
        refine ⟨⟨m1, rfl, rfl, Or.inl ⟨rfl, fun x g h => by cases h⟩⟩, fun h => by simp [s1] at h, fun t m ht hm hl => ?_⟩
        rcases mem_E hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [vs1, s1] at ht
      | n + 1, hv => simp at hv
    · intro o ht; exact absurd ht twoAt_int
  -- PromLt
  · intro t ht; cases ht
  -- FreshLP
  · intro j _
    refine ⟨?_, fun t m hm hl => ?_, ?_, ?_, ?_⟩
    · simp only [E, freshLabel, g0]; split
      · rename_i h; have h' : (8 + 0 + 1 * j : Nat) = 7 := h; omega
      · rfl
    · rcases mem_E hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (have h' : (7 : Nat) = 8 + 0 + 1 * j := hl; omega)
    · rfl
    · rfl
    · simp only [E, freshLabel, g0]; split
      · rename_i h; have h' : (8 + 0 + 1 * j : Nat) = 7 := h; omega
      · rfl
  · rintro t m _ _ ⟨c, N, e, us, hc, -, -, ho, -⟩; obtain ⟨-, rfl⟩ := sto_E hc; cases ho
  -- SeenLE
  · intro l h; cases h
  -- OwnHidP: the placeholder at t0 is hidden by t1 ≤ vWr = 1; no count gap (ini = 0)
  · intro l c hc _ o _ t m _ hm hl hno
    obtain ⟨rfl, rfl⟩ := sto_E hc
    rcases mem_E hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨1, m1, by decide, Nat.le_refl _, rfl, hl⟩
    · exfalso; apply hno
      have ho : o = 0 := (congrArg Address.offset hl).symm
      subst ho; exact wordOK_m1 E
  · intro l c _ _ hlt
    have h1 := E.rc_le_ini l
    have h2 : E.ini l = 0 := rfl
    omega
  -- PubDefP (the only cell is own)
  · intro l c f hc ho; obtain ⟨-, rfl⟩ := sto_E hc; exact absurd rfl ho
  -- OwnPubV: f = 1 ≤ vWr = 1
  · intro l c f hc _ hf
    obtain ⟨rfl, rfl⟩ := sto_E hc
    have hf1 : f = 1 := (Option.some.inj hf).symm
    subst hf1; exact Or.inr (Or.inl (Nat.le_refl _))
  -- PubInv: SeenOwn, Inh, PubCpl, PubMem
  · intro l h; cases h
  · intro l c b S us hc hS hus _
    obtain ⟨-, rfl⟩ := sto_E hc; obtain ⟨-, rfl⟩ := seg_int hS
    rw [accs_int] at hus; cases hus
    exact ⟨[⟨.num 0, 0, 0⟩], (valOf_num E _ 0 rfl).1, rfl⟩
  · intro l c f hc _
    obtain ⟨-, rfl⟩ := sto_E hc
    refine ⟨Or.inl (by decide), fun b S hS _ => ?_, by decide, by decide, by decide⟩
    obtain ⟨-, rfl⟩ := seg_int hS; exact TearOK_of_cplB (by decide)
  · intro l c f o hc _ _ ht; exact absurd (by obtain ⟨-, rfl⟩ := sto_E hc; exact ht) twoAt_int
  · intro l c f b S us o hc ho; obtain ⟨-, rfl⟩ := sto_E hc; exact absurd rfl ho
  -- BoxInv
  · refine ⟨fun _ _ => rfl, fun l B h => ?_, fun l B h => ?_⟩ <;> simp [E] at h
  -- PromOK
  · refine ⟨List.nodup_nil, fun t h => ?_, fun t h => ?_⟩ <;> cases h


theorem cohB : CohBW E := fun _ =>
  ⟨Clo_void, fun _ _ _ => by simp [E, CE, VRF, VRb2], fun _ _ _ => by simp [E, CE, TEnv.unsee, VRF, VRb2]⟩

theorem iniAt_int (ini : AllocLabel → Nat) : IniAt ini cO ⟨7, 0⟩ .int :=
  IniAt_of_ne fun N e h => by cases h

/-- The address word is ♭-typed (flag False at top, `False ∨ IniAt rc` at the `.loc` arm) via the owner exemption. -/
theorem vr_word (ρ : Nat → Nat) : (VRF False) ρ E (.loc .pub .int) (shp (.loc .pub .int)) [pw] := by
  simp only [VRF, VRb2]
  refine Or.inr ⟨⟨7, 0⟩, cO, .int, rfl, rfl, .here (Or.inl (show accs Ty.int ≠ none by rw [accs_int]; simp)), .refl, ?_, iniAt_int _⟩
  exact ⟨1, rfl, Or.inr (Or.inr ⟨rfl, Or.inr (iniAt_int _)⟩)⟩

/-- Without the exemption (flag False) the word is not typed: view 0 < frontier 1, unseen. -/
theorem not_modeOKb : ¬ ModeOKb E.tid E.pfr E.seen False .pub 7 cO [pw] := by
  rintro ⟨f, hf, hs | hv | ⟨-, hb⟩⟩
  · exact hs
  · have hf1 : f = 1 := (Option.some.inj hf).symm
    subst hf1
    exact absurd (hv pw (List.mem_singleton.mpr rfl)) (by decide)
  · exact hb

/-- **Non-vacuity at MemInvB**: the owner branch of `tstepM_loadCellLocB` (`locLoadIB`, its frontier premise
discharged from the exempt `ModeOKb` exactly as in that proof) runs at the witness: loads exist and every result
is ♭-typed. -/
theorem witness (ρ : Nat → Nat) :
    ∃ us, accs Ty.int = some us ∧ (∃ r, r ∈ loadUnits .arm pw ⟨7, 0⟩ false us 0 s1) ∧
      (∀ r, r ∈ loadUnits .arm pw ⟨7, 0⟩ false us 0 s1 → PromAbove r.1 →
        (VRF False) ρ E .int (shp .int) r.2 ∧ Lay [] .int .int r.2 ∧ r.1.mem = s1.mem ∧ r.1.pairs = s1.pairs ∧
        LoadCohB (CE E) s1 r.1 ∧ r.1.promises = s1.promises ∧ r.1.nalloc = s1.nalloc) ∧
      ∃ ws, (VRF False) ρ E .int (shp .int) ws ∧ Lay [] .int .int ws := by
  have hm : MemInvB g0 (CE E) s1 := memInvB
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (u := Ty.int) (rfl : CoreTerm.cellOf (Ty.loc Mode.pub Ty.int) = some (Mode.pub, Ty.int))
      (fun n e h => by cases h) (vr_word ρ)
  obtain rfl : ad = ⟨7, 0⟩ := by
    simp only [pw, List.map, List.cons.injEq, Val.loc.injEq] at hws; exact hws.1.1.symm
  obtain ⟨-, rfl⟩ := sto_E hsto
  exact locLoadIB (σs := []) (ru := .int) (u := .int) (arch := .arm) (pw := pw) (acq := false) (s := s1)
    cohB hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.1 hsto rfl hat hini
    (fun N e h => by cases h)
    (fun hir f hf hns => by
      obtain ⟨f0, hf0, hsf⟩ := hmode
      obtain rfl : f0 = f := Option.some.inj (hf0.symm.trans hf)
      rcases hsf with hs | hs | ⟨-, hb⟩
      · exact absurd hs hns
      · exact hs pw (by simp)
      · exact absurd (hb.resolve_left id) hir)
    rfl rfl rfl rfl

end OwnerExemptWitness
#print axioms OwnerExemptWitness.memInvB
#print axioms OwnerExemptWitness.vr_word
#print axioms OwnerExemptWitness.not_modeOKb
#print axioms OwnerExemptWitness.witness
