import WeakCore.TermInterf
import WeakCore.TermPlantF

/-!
# TermPlantHidOf: `plantHid` (P4b clause 7's planted half) is a theorem

At a promise step planting the promiser's private cell `l` at frontier `f = plantF`, the
promiser's own post-step invariant (`selfPlant`: `MemInv` at its cut of `EgP`) has `OwnHidP`:

* if the plant raised the reader-visible count past the real one (`rc < ini`), part 2 hides
  every reader-visible slot below the cell's frontier, which is `f`;
* otherwise every reader-visible slot is a real one, and part 1 hides it below `vWr ≤ f`
  (`plantF = max vWr plantT`).

Both skip the promiser's outstanding promises (old and the new one); those are typed in `PubE`
after the step (`PromTyAPostPF`), so they are never the `¬ WordOK` message.  A word typed in the
promiser's cut is typed in `PubE` (`InclS_cut_pub`, the cell is `noOR` by `PlantSpec`).
-/

namespace TermPlantHidOf
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermInterf
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open TermFul

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`PlantHidF` at `TermPlantF.plantOf`/`plantN`**, from `PlantSpec`, the promiser's
post-step part (`selfPlant`'s shape) and the promise typing after the step. -/
theorem plantHid_of
    (hspec : PlantSpecF p k arch Sp Init MintOK c0 TermPlantF.plantOf)
    (hself : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
      {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts},
      PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      (∃ l f, TermPlantF.plantOf c Eg j a v w l = some f) →
      ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
        ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
          (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
          (Tot j) HP' HS' cr' db')
    (hpa : PromTyAPostPF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN) :
    PlantHidF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN := by
  intro c Eg Tot HP HS cr db j th a v w X l f cl hf hs o hio
  obtain ⟨-, -, -, -, -, S, -, -, hm, -⟩ := hself X ⟨l, f, hf⟩
  obtain ⟨-, ⟨cl0, hs0, ho0⟩, -, hnoor⟩ := hspec X l f hf
  rw [hs] at hs0; cases hs0
  have hown : cl.owner = some j := ho0
  -- the promiser's cut of `EgP`
  have hsE : (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
      (gOf p k arch c j).i S).sto l = some cl := cutSto_own (by simp only [EgP, GEnv.withFp, plantG]; exact hs) hown
  have hpfrG : (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size).pfr l = some f := by
    simp only [EgP, GEnv.withFp, plantG, hf]
  have hshG : (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size).Shared l :=
    ⟨f, hpfrG⟩
  have hoh := hm.2.2.2.2.2.1
  -- hidden in the promiser's cut, skipping its promises
  have hid : HiddenP (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
      (gOf p k arch c j).i S) cl.ty (c.mem.push ⟨a, v, w⟩) (th.promises ++ [c.mem.size]) l o f := by
    by_cases hlt : (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (gOf p k arch c j).i S).rc l <
        (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (gOf p k arch c j).i S).ini l
    · obtain ⟨f', hf', -, hH⟩ := hoh.2 l cl hsE hown hlt
      have e : f' = f := Option.some.inj (hf'.symm.trans hpfrG)
      subst e
      exact hH o hio
    · have hrr : InitRr (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
          (gOf p k arch c j).i S) cl l o := by
        intro N e us h1 h2
        have h3 := hio N e us h1 h2
        have h4 := TEnv.rc_le_ini (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
          (gOf p k arch c j).i S) l
        have h5 : (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
            (gOf p k arch c j).i S).rc l =
            (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
            (gOf p k arch c j).i S).ini l := Nat.le_antisymm h4 (Nat.le_of_not_lt hlt)
        rw [h5]; exact h3
      have hH := hoh.1 l cl hsE hown o hrr
      have hvf : th.vs.vWr ≤ f := by
        obtain ⟨-, rfl⟩ := TermPlantF.plantOf_some X.hth hf
        exact Nat.le_max_left _ _
      intro t m hn hm1 hl hw
      obtain ⟨t', m', h1, h2, h3, h4⟩ := hH t m hn hm1 hl hw
      exact ⟨t', m', h1, Nat.le_trans h2 hvf, h3, h4⟩
  -- promises are typed in `PubE`; other messages are hidden
  obtain ⟨epc, hpj, -⟩ := promise_inv (a := a) (v := v) (w := w) X.hth
  have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [epc]
  intro t m _ hm1 hl hw
  by_cases ht : t ∈ th.promises ++ [c.mem.size]
  · have hm2 : (promise c j a v w).mem[t]? = some m := by rw [hmem]; exact hm1
    have hcl : (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size).sto m.loc.label
        = some cl := by rw [hl]; simp only [EgP, GEnv.withFp, plantG]; exact hs
    have hsh : (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size).Shared
        m.loc.label := by rw [hl]; exact hshG
    have hW := hpa X j _ t m hpj ht hm2 cl hcl hsh
    rw [hl] at hW
    exact absurd hW hw
  · exact hid t m ht hm1 hl (fun h => hw (WordOK_transferS (InclS_cut_pub _ _ S) (hnoor cl hs) h))

end

end TermPlantHidOf

#print axioms TermPlantHidOf.plantHid_of
