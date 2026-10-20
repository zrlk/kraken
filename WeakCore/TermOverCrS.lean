import WeakCore.TermOverCrR
import WeakCore.TermBlkZ

/-! # TermOverCrS: the foreign-store cover at the post-step plant transfer (H7)

TermMain's plant transfer `Pδ` (H7) states each target's plant credit in the POST-step state.
`foreign_overCrP` is `foreign_overCr` with its target premise in that form: the holder
lowness the new items need is read off the post-step credit (`plantCr_low`) and carried back
along the step (the idle thread's promises are unchanged, memory keeps its prefix).
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **Holder lowness before the step from a plant credit after it.** -/
theorem plantCr_low_back {E' : TEnv} {s s' : St} {m : Msg} {t : Ts} {R : Res} {c : Cell} {b : Nat}
    {S : Ty} {us : List Acc}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hPl : PlantCr E' s' m t R) (hsto : E'.sto m.loc.label = some c) (hpc : TermPiece.Piece c.ty b S)
    (hus : accs S = some us) (h1 : b ≤ m.loc.offset) (h2 : m.loc.offset < b + nWords us) :
    ∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = m.loc.label →
      b ≤ m'.loc.offset → m'.loc.offset < b + nWords us → t ≤ t' := by
  intro t' m' ht hm hl h1' h2'
  exact plantCr_low hPl hsto hpc hus h1 h2 t' m' (by rw [hpr]; exact ht)
    (by rw [hpre t' (hP t' ht)]; exact hm) hl h1' h2'

#print axioms plantCr_low_back

/-- `HolderLow` for the new items from per-target lowness in the entry's piece. -/
theorem holderLow_dnOfL {s : St} {l : AllocLabel} {tg : TermPiece.GdE → Option Ts}
    {Kf : TermPiece.GdE → Nat → Bool} {Gd : List TermPiece.GdE}
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∀ us, accs g.S = some us →
      ∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = l →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') :
    TermOverCr.HolderLow s l (dnOf l tg Kf Gd) := by
  intro y hy usS hus t' m' ht hm hl h1 h2
  obtain ⟨g, hg, hgl, t, htg, rfl⟩ := mem_dnOf.1 hy
  exact hT g hg hgl t htg usS hus t' m' ht hm hl h1 h2

#print axioms holderLow_dnOfL

/-- **A drop entry's payload carries no own key** (`CrKeys`, Pδ's key clause): the entry's piece
lies in a cell with a frontier, whose type is own-free (`MemInv_noOwnT`), hence so is the piece. -/
theorem crKeys_gd {g0 : G} {E : TEnv} {s : St} {g : TermPiece.GdE} {f : Ts}
    (hm : MemInv g0 E s) (hok : TermPiece.GdOK E s g) (hf : E.pfr g.l = some f) : TermPlant.CrKeys g.R := by
  obtain ⟨c, hsto, -, -, hP, -, -, hv⟩ := hok
  have hno : Ty.noOwnIn [] g.S = true := noOwn_AtOff hP.1 (MemInv_noOwnT hm hsto hf)
  exact fun l => TermBlkZ.VRR_own_zero l g.S [] (CE E.unsee) (fun _ => 0) (shp g.S) g.ws g.R hno
    (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h) hv.1

#print axioms crKeys_gd

/-- **(H7 htg, pre-state half) The piece-lowest own promise takes the entry's payload**: on top of
its `PromCrK` credit, as a key-free plant credit, at the lowest own promise of the entry's piece
(below a window bound clearing the foreign promises). -/
theorem pd_pre {E : TEnv} {s : St} {cr db : Ts → Res} {l : AllocLabel} {c : Cell} {g : TermPiece.GdE}
    {us : List Acc} {tw wb : Ts} {mw : Msg}
    (hC : TermPlant.PromCrK E s cr db)
    (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hpf : E.pfr l ≠ none) (hlay : LayT c.ty)
    (hP : TermPiece.Piece c.ty g.b g.S) (hus : accs g.S = some us)
    (hnw : ∀ o', g.b ≤ o' → o' < g.b + nWords us → ¬ WordUnit E ⟨l, o'⟩)
    (htw : tw ∈ s.promises) (hmw : s.mem[tw]? = some mw) (hlw : mw.loc.label = l)
    (h1 : g.b ≤ mw.loc.offset) (h2 : mw.loc.offset < g.b + nWords us) (hwbt : tw ≤ wb) (hwb : wb < s.mem.size)
    (hfp : ∀ tf mf, tf ∈ FpAt E ⟨l, 0⟩ → s.mem[tf]? = some mf → mf.loc.label = l → wb < tf)
    (hwl : g.ws.length = nWords us) (hv : ValOfR E g.S g.ws g.R) (hK : TermPlant.CrKeys g.R) :
    ∃ t m, t ∈ s.promises ∧ s.mem[t]? = some m ∧ m.loc.label = l ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us ∧ t ≤ tw ∧
      PlantCr E s m t (cr t + g.R) ∧ TermPlant.CrKeys (cr t + g.R) := by
  obtain ⟨t, m, ht, hm, hl, hb1, hb2, hle, -, hpc⟩ := piece_target (R0 := g.R) (R := g.R) hsto hown hpf hlay hP
    hus hnw htw hmw hlw h1 h2 hwbt hwb hfp hwl hv (Res.le_refl _)
  have hw : ¬ WordUnit E m.loc := by
    have := hnw m.loc.offset hb1 hb2
    rw [← hl] at this
    exact this
  exact ⟨t, m, ht, hm, hl, hb1, hb2, hle, plantCrK_add hC ht hm hw hpc hK⟩

#print axioms pd_pre

/-- **(H7 htg, pre-state) A target for an entry at a guarded lowest own promise**: the label-wide
window guard at the unit's lowest own promise `tw` is the window bound `pd_pre` needs.  (F3: the
cover's guard is per unit, `WinG`; this needs the label-wide `WinGL`, as `PlantCr`'s footprint
clause is label-wide.) -/
theorem htg_pre {E : TEnv} {s : St} {cr db : Ts → Res} {l : AllocLabel} {c : Cell} {g : TermPiece.GdE}
    {us : List Acc} {o : Nat} {tw : Ts}
    (hC : TermPlant.PromCrK E s cr db)
    (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hpf : E.pfr l ≠ none) (hlay : LayT c.ty)
    (hP : TermPiece.Piece c.ty g.b g.S) (hus : accs g.S = some us)
    (hnw : ∀ o', g.b ≤ o' → o' < g.b + nWords us → ¬ WordUnit E ⟨l, o'⟩)
    (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) (hW : TermOverCr.WinGL E s l tw)
    (h1 : g.b ≤ o) (h2 : o < g.b + nWords us)
    (hwl : g.ws.length = nWords us) (hv : ValOfR E g.S g.ws g.R) (hK : TermPlant.CrKeys g.R) :
    ∃ t m, t ∈ s.promises ∧ s.mem[t]? = some m ∧ m.loc.label = l ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us ∧ t ≤ tw ∧
      PlantCr E s m t (cr t + g.R) ∧ TermPlant.CrKeys (cr t + g.R) := by
  obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := hl
  have hlw : mw.loc.label = l := by rw [hml]
  have ho : mw.loc.offset = o := by rw [hml]
  exact pd_pre hC hsto hown hpf hlay hP hus hnw htw hmw hlw (by rw [ho]; exact h1) (by rw [ho]; exact h2)
    (Nat.le_refl _) (lt_size_of_some hmw) (fun tf mf h0 h3 h4 => hW.2 tf mf h0 h3 h4) hwl hv hK

#print axioms htg_pre

end TermOverCrW
