/-
**The lowered code blocks' phase premises from `PlaceOK`** (x86-64): A9's
phase part (`fnPhOk`, `Spike/Lib/LowerX64/PhCheck.lean`) gives, at every
`func0`-shaped function of the output's IR, the prologue's `ProPh`
(`Spike/Lib/LowerX64/UserW.lean`) and the body's `bodyPhOk` at A6's tables
(`okPcOf`, `phOf`: the phase record's `okPc`, `ph`) and the loader's labels,
the return address the label after `scc_rt_main`'s `call`.

- `proPh_of_proPhOk`: the Boolean form gives `ProPh`;
- `fnPh1_sound`: one function's check at the code labels (`labC`) gives
  its premises at any label map agreeing with the code labels where they
  resolve (`hlab`; the loader's, `label_threadAt_of_codeLabel`), every label
  the check reads resolving;
- `userPh_of_placeOK`: at a `func0` block of a placed output, the prologue
  at the listing's sizes (`proInC`) with its `ProPh`, with an instruction
  the local overflow block's `blkPh` (`Local.lb` at `ovfL`: `hab_of`'s
  `hphA`), and `bodyPhOk`.
-/
import Spike.Lib.LowerX64.UserW
import Spike.Lib.LowerX64.PhCheck
import Spike.Lib.LowerX64.OvfCode
import Scc.Cert.PlaceOKX64

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.X64.Flow (xHead xLea xCmp xFr)
open Scc.Emit.X64 (labelOf)
open Scc.Sem.X64 (codeLabel)

/-- **The Boolean form gives `ProPh`.** -/
theorem proPh_of_proPhOk {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {fn sc : Label} {Z : Int64}
    {L : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (h : proPhOk okPc ph lab fn sc Z L zl zf z1 z2 zs ps = true) : ProPh okPc ph lab fn sc Z L zl zf z1 z2 zs ps := by
  simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hd, lea⟩, ld1⟩, ld2⟩, cmp⟩, fr⟩ := h
  exact ⟨hd, lea, ⟨ld1, ld2⟩, cmp, fr⟩

/-- A resolved label's `labC` is its address under any map agreeing with
the code labels. -/
theorem labC_eq {lo : Nat} {cells : List (Directive × Nat)} {lab : Label → Int64}
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a) {l : String}
    (hr : (codeLabel lo cells l).isSome = true) : labC lo cells l = lab l := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hr
  rw [labC, ha, hlab l a ha]; rfl

/-- `blkPh` at the code labels is `blkPh` at `lab`, every label it reads
resolving. -/
theorem blkPh_labC {lo : Nat} {cells : List (Directive × Nat)} {lab : Label → Int64}
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool} {ph : Nat → Nat}
    {dead : Nat → Bool} {pc ra : Int64} {blk : List (Directive × Nat)}
    (hr : (blkLabs blk).all (fun l => (codeLabel lo cells l).isSome) = true) :
    blkPh okPc ph dead (labC lo cells) pc ra blk = blkPh okPc ph dead lab pc ra blk :=
  blkPh_congr fun L hL => labC_eq hlab (List.all_eq_true.mp hr L hL)

/-- **One function's check gives its premises** at `lab`: the prologue's
`ProPh` at the listing's sizes and the body's `bodyPhOk`. -/
theorem fnPh1_sound {okPc : Nat → Bool} {ph : Nat → Nat} {lo : Nat} {cells : List (Directive × Nat)}
    {lab : Label → Int64} (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {fr : Scc.Emit.X64.Frame} {fn : String} {is : List Scc.IR.Inst} {w : Scc.IR.Operand} {ra : Int64}
    (h : fnPh1 okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr fn is w ra = true) :
    ∃ zl zf z1 z2 zs, sizesAt cells (labelOf fr.fn "chk") 0 5 = [zl, zf, z1, z2, zs] ∧
      ProPh okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [] ∧
      (is ≠ [] → blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 ovfBlk = true) ∧
      bodyPhOk okPc ph (fun _ => false) lab cells fr (labelOf fn "entry") is [w] ra = true := by
  unfold fnPh1 at h
  split at h
  · next zl zf z1 z2 zs hs =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨rfn, rsc⟩, ren⟩, rpro⟩, rbody⟩, hpro⟩, hovf⟩, hbody⟩ := h
    refine ⟨zl, zf, z1, z2, zs, hs, ?_, ?_, ?_⟩
    · have hpr := List.all_eq_true.mp rpro
      have e := fun (blk : List (Directive × Nat)) (hsub : ∀ L ∈ blkLabs blk, L ∈ proLabs (Int64.ofInt fr.size)
          (proL fr) zl z1 z2 zs []) =>
        blkLabs_all_of (fun L hL => hpr L (hsub L hL))
      apply proPh_of_proPhOk
      simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at hpro ⊢
      rw [labC_eq hlab rfn, labC_eq hlab rsc] at hpro
      obtain ⟨⟨⟨⟨⟨hd, lea⟩, ld1⟩, ld2⟩, cmp⟩, frr⟩ := hpro
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ld1⟩, ld2⟩, ?_⟩, ?_⟩
      · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact hd
      · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact lea
      · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact cmp
      · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact frr
    · intro hne
      simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true] at hovf
      obtain ⟨⟨rab, rlb⟩, hb⟩ := hovf.resolve_left hne
      rw [labC_eq hlab rab, blkPh_labC hlab rlb] at hb
      exact hb
    · unfold bodyPhOk at hbody ⊢
      rw [List.all_eq_true] at hbody rbody ⊢
      intro x hx
      have := hbody x hx
      rw [labC_eq hlab ren, blkPh_labC hlab (rbody x hx)] at this
      exact this
  · cases h
where
  blkLabs_all_of {lo : Nat} {cells : List (Directive × Nat)} {blk : List (Directive × Nat)}
      (h : ∀ L ∈ blkLabs blk, (codeLabel lo cells L).isSome = true) :
      (blkLabs blk).all (fun l => (codeLabel lo cells l).isSome) = true :=
    List.all_eq_true.mpr h

open Scc.Cert.PlaceOK.X64 in
/-- **The user functions' phase premises from `PlaceOK`**: at a `func0`
block of a placed output, its prologue at the listing's sizes (`proInC`)
with its `ProPh`, and its body's `bodyPhOk`, at A6's `okPcOf`/`phOf`, any
label map agreeing with the code labels (`hlab`), the return address the
label after `scc_rt_main`'s `call`. -/
theorem userPh_of_placeOK {cfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt cfg Λ o = true)
    {ir : Scc.IR.Program} (hir : o.place.ir = some ir) {lab : Label → Int64}
    (hlab : ∀ l a, codeLabel Λ.code.lo o.prog l = some a → lab l = Int64.ofNat a)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} (hf : Scc.Lower.Inv.func0 name r ∈ ir.funcs)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    let fr := frOf ir (Scc.Lower.Inv.func0 name r)
    let okPc := Scc.Cert.Rt.X64.okPcOf Λ.code.lo o.prog Λ
    let ph := Scc.Cert.Rt.X64.phOf Λ.code.lo o.prog
    ∃ zl zf z1 z2 zs, proInC o.prog fr name (labelOf name "entry") zl zf z1 z2 zs = true ∧
      ProPh okPc ph lab name (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [] ∧
      (r.insts ≠ [] → blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0
        Spike.Lib.X64.Abort.Local.lb = true) ∧
      bodyPhOk okPc ph (fun _ => false) lab o.prog fr (labelOf name "entry") r.insts [w] (lab raL) = true := by
  intro fr okPc ph
  obtain ⟨ir', hir', hok⟩ := fnCodeOk_of_placeOKAt h
  rw [hir] at hir'; cases hir'
  have hS := fnCodeOk_func0_proInS hok hf hI hw
  obtain ⟨hra, hall⟩ := fnPhOk_parts (fnPh_of_placeOKAt h hir)
  have h1 := fnPhAll_func0 hall hf hI hw
  rw [labC_eq hlab hra] at h1
  obtain ⟨zl, zf, z1, z2, zs, hs, hpro, hovf, hbody⟩ := fnPh1_sound hlab h1
  refine ⟨zl, zf, z1, z2, zs, ?_, hpro, ovfBlk_eq_lb ▸ hovf, hw ▸ hbody⟩
  unfold proInS at hS
  rw [hs] at hS
  exact hS

end Spike.Lib.LowerX64
