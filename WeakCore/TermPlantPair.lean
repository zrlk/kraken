import WeakCore.TermInterf
import WeakCore.TermPlantF

/-!
# TermPlantPair: `plantPair` (P4b clause 9d's planted half) is a theorem

At a promise step planting the promiser's private cell `l` at frontier `f = plantF`, take a
two-word unit `o` in a segment below the planted `ini` and two messages at its words that a
reader bounded by `f` may pair.  Neither is a promise (`PromNoTwoOK`, `PromNoTwoPF`).  In the
promiser's post-step invariant (`selfPlant`: `MemInv` at its cut of `EgP`):

* a slot past the real count (a predicted slot) is `PubPair`'s planted disjunct;
* a real slot is `OwnPairF` (the cell now has a frontier): the two messages are at or past
  coherence, since the coherence message is at most `vWr ≤ f` (`OwnCohZ`, the cell private
  before the step) and would hide anything below it.  So they are the coherence pair holding
  the cell's words (a pair of one value by `CellOK_seg`) or a pair of one value.

A pair typed in the promiser's cut is typed in `PubE` (`PairOK_transferS`, the cell `noOR`).
-/

namespace TermPlantPair
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermInterf
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- A two-word unit in a real-initialised segment is real-initialised. -/
theorem initRr_of_seg {E : TEnv} {c : Cell} {l : AllocLabel} {b o' : Nat} {S : Ty} {us : List Acc}
    (hi : IniSegN (E.rc l) c b) (hseg : SegOf c.ty b S) (hus : accs S = some us) (ho : o' < nWords us) :
    InitRr E c l (b + o') := by
  intro N e us2 hT hus2
  obtain ⟨us', j, hus', hj, rfl⟩ := hi N e hT
  obtain rfl : us2 = us' := by rw [hus2] at hus'; exact Option.some.inj hus'
  rcases hseg with ⟨-, rfl, -⟩ | ⟨N', us3, j', hT', hus3, -, -⟩
  · rw [hT] at hus; simp [accs] at hus
  · rw [hT] at hT'; simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
    obtain ⟨-, rfl⟩ := hT'
    obtain rfl : us2 = us := by rw [hus2] at hus; exact Option.some.inj hus
    have h1 : (j + 1) * nWords us2 ≤ E.rc l * nWords us2 := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at h1
    omega

/-- A message below the coherence message, which lies within the bound, is hidden. -/
theorem hidden_of_coh {mem : Memory} {a : Address} {t tc f : Nat} {mc : Msg} (hlt : t < tc) (hcf : tc ≤ f)
    (hmc : mem[tc]? = some mc) (hl : mc.loc = a) : WeakMem.hiddenFrom mem a t f = true := by
  unfold WeakMem.hiddenFrom
  rw [List.any_eq_true]
  refine ⟨tc, List.mem_range.2 (Nat.lt_succ_of_le hcf), ?_⟩
  simp [hlt, hmc, hl]

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`PlantPairF` at `TermPlantF.plantOf`/`plantN`**, from `PlantSpec`, the promiser's
post-step part (`selfPlant`'s shape) and `PromNoTwoPF`. -/
theorem plantPair_of
    (hspec : PlantSpecF p k arch Sp Init MintOK c0 TermPlantF.plantOf)
    (hself : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
      {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts},
      PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      (∃ l f, TermPlantF.plantOf c Eg j a v w l = some f) →
      ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
        ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
          (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
          (Tot j) HP' HS' cr' db')
    (hnt : PromNoTwoPF p k arch Sp Init MintOK c0) :
    PlantPairF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN := by
  intro c Eg Tot HP HS cr db j th a v w X l f cl hf hs o hTw hg t0 t1 m0 m1 h0 h1 hl0 hl1 hh0 hh1 hps
  obtain ⟨-, -, -, -, -, S, -, -, hm, -⟩ := hself X ⟨l, f, hf⟩
  obtain ⟨hpn0, ⟨cl0, hs0, ho0⟩, -, hnoor⟩ := hspec X l f hf
  rw [hs] at hs0; cases hs0
  have hown : cl.owner = some j := ho0
  have hsE : (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
      (gOf p k arch c j).i S).sto l = some cl := cutSto_own (by simp only [EgP, GEnv.withFp, plantG]; exact hs) hown
  have hpfrG : (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size).pfr l = some f := by
    simp only [EgP, GEnv.withFp, plantG, hf]
  -- no message at the unit is a promise (old: `PromNoTwoOK`; the new one: `PromNoTwoPF`)
  have hnp : ∀ (t : Nat) (m : Msg), (c.mem.push ⟨a, v, w⟩)[t]? = some m → (m.loc = ⟨l, o⟩ ∨ m.loc = ⟨l, o + 1⟩) →
      t ∉ th.promises ++ [c.mem.size] := by
    intro t m ht hl hp
    have hcl : Eg.sto m.loc.label = some cl := by rcases hl with e | e <;> (rw [e]; exact hs)
    rcases push_get ht with ⟨-, h2⟩ | ⟨-, rfl⟩
    · rcases List.mem_append.1 hp with hp | hp
      · have h3 := X.inv.promNoTwo j th t m cl X.hth hp h2 hcl o hTw
        rcases hl with e | e
        · exact h3.1 (by rw [e])
        · exact h3.2 (by rw [e])
      · simp only [List.mem_singleton] at hp
        subst hp
        exact absurd h2 (by simp)
    · have h3 := hnt X cl hcl o hTw
      rcases hl with e | e
      · exact h3.1 (by rw [show a = ⟨l, o⟩ from e])
      · exact h3.2 (by rw [show a = ⟨l, o + 1⟩ from e])
  have hn0 := hnp t0 m0 h0 (.inl hl0)
  have hn1 := hnp t1 m1 h1 (.inr hl1)
  refine PairOK_transferS (InclS_cut_pub (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j
    c.mem.size) (gOf p k arch c j).i S) (hnoor cl hs) ?_
  obtain ⟨b, S', us, o', hseg, hus, htw, rfl, hini⟩ := hg
  have hlt2 := TwoAt_lt htw
  by_cases hr : IniSegN ((Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
      (gOf p k arch c j).i S).rc l) cl b
  · -- a real slot: `OwnPairF`
    have hrr := initRr_of_seg hr hseg hus (show o' < nWords us by omega)
    obtain ⟨vals, hcv, hlat, hpair⟩ := hm.2.1 l cl hsE hown
    have hcov0 := CellOK_cover hcv hseg hus (show o' < nWords us by omega)
    have hcov1 := CellOK_cover hcv hseg hus (show o' + 1 < nWords us by omega)
    have hvf : th.vs.vWr ≤ f := by
      obtain ⟨-, rfl⟩ := TermPlantF.plantOf_some X.hth hf
      exact Nat.le_max_left _ _
    have hoc := X.inv.ownCoh j th (fun _ => False) X.hth l cl (cutSto_own hs hown) hown hpn0
    have hcoh : ∀ (o1 t : Nat) (m : Msg), o1 < vals.length → (c.mem.push ⟨a, v, w⟩)[t]? = some m →
        m.loc = ⟨l, o1⟩ → WeakMem.hiddenFrom (c.mem.push ⟨a, v, w⟩) ⟨l, o1⟩ t f = false →
        th.vs.coh ⟨l, o1⟩ ≤ t := by
      intro o1 t m hlt hmt hl hh
      obtain ⟨⟨mc, hmc, hlc, -⟩, -, -⟩ := hlat o1 _ (List.getElem?_eq_getElem hlt)
      refine Nat.le_of_not_lt fun hlt' => ?_
      have hcf : th.vs.coh ⟨l, o1⟩ ≤ f := Nat.le_trans (hoc o1 ⟨_, _, vals, hcv, hlt⟩) hvf
      have h2 : WeakMem.hiddenFrom (c.mem.push ⟨a, v, w⟩) ⟨l, o1⟩ t f = true := hidden_of_coh hlt' hcf hmc hlc
      rw [hh] at h2; cases h2
    rcases hpair (by rw [show (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j
        c.mem.size) (gOf p k arch c j).i S).pfr l = some f from hpfrG]; simp) (b + o')
        ⟨b, S', us, o', hseg, hus, htw, rfl⟩ hrr t0 t1 m0 m1 hn0 hn1 h0 h1 hl0 hl1
        (hcoh _ t0 m0 hcov0 h0 hl0 hh0) (hcoh _ t1 m1 (by omega) h1 hl1 (by rw [Nat.add_assoc] at hh1 ⊢; exact hh1))
        hps with ⟨-, -, hw0, hw1⟩ | hok
    · have hV := (CellOK_seg hcv hseg hus hr).1
      refine ⟨b, S', (vals.drop b).take (nWords us), o', vals[b + o'], vals[b + o' + 1], hseg, hV, ?_, ?_,
        hw0 _ (List.getElem?_eq_getElem hcov0), hw1 _ (List.getElem?_eq_getElem hcov1), rfl⟩
      · rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
        exact List.getElem?_eq_getElem hcov0
      · rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, ← Nat.add_assoc]
        exact List.getElem?_eq_getElem hcov1
    · exact hok
  · -- a predicted slot: `PubPair`'s planted disjunct
    have hrc : (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (gOf p k arch c j).i S).rc l <
        (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (gOf p k arch c j).i S).ini l :=
      Nat.lt_of_not_le fun hle => hr (hini.mono hle)
    exact hm.2.2.2.2.2.2.2.2.1.2.2.2.1 l cl f (b + o') hsE
      (.inr ⟨hrc, b, S', us, o', hseg, hus, htw, rfl, hr, hini⟩) hpfrG hTw t0 t1 m0 m1 hn0 hn1 h0 h1 hl0 hl1 hh0 hh1 hps

end

end TermPlantPair

#print axioms TermPlantPair.plantPair_of
