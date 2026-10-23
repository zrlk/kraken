/-
**The lowered code blocks' phase premises from `PlaceOK`** (AArch64): A9's
phase part (`fnPhOk`, `Spike/Lib/LowerA64/PhCheck.lean`) gives, at every
`func0`-shaped function of the output's IR, the prologue's `ProPh`
(`Spike/Lib/LowerA64/UserW.lean`) and the body's `bodyPhOk`
(`Spike/Lib/LowerA64/BodyW.lean`) at A6's tables (`okPcOf`, `phOf`: the
phase record's `okPc`, `ph`) and the loader's labels, the return address
after `scc_rt_main`'s `bl` (`.L1_scc_rt_main.0_entry` plus 4).

- `proPh_of_proPhOk`: the Boolean form gives `ProPh`;
- `fnPh1_sound`: one function's check at the code labels (`labC`) gives
  its premises at any label map agreeing with the code labels where they
  resolve (`hlab`; the loader's, `label_threadAt_of_codeOf`), every label
  the check reads resolving;
- `userPh_of_placeOK`: at a `func0` block of a placed output, the
  prologue's `ProPh`, with an instruction the local overflow block's
  `blkPh` (`Local.lb`: `hab_of`'s `hphA`), and the body's `bodyPhOk`.
-/
import Spike.Lib.LowerA64.UserW
import Spike.Lib.LowerA64.PhCheck
import Spike.Lib.LowerA64.OvfCode
import Scc.Cert.PlaceOKA64

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (blkPh)
open Scc.Emit.A64
open Scc.Cert.Link.A64 (codeOf)

/-- **The Boolean form gives `ProPh`.** -/
theorem proPh_of_proPhOk {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {sc : Label} {Z : Int64}
    {L : Label} {ps : List (XReg × Int64)} (h : proPhOk okPc ph lab sc Z L ps = true) :
    ProPh okPc ph lab sc Z L ps := by
  simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hd, ld1⟩, ld2⟩, br⟩, fr⟩ := h
  exact ⟨hd, ⟨ld1, ld2⟩, br, fr⟩

/-- `fnPh1`'s body conjunct is `bodyPhOk`. -/
theorem bodyPhOk_eq {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {cx : FnCtx} {l : Label}
    {is : List Scc.IR.Inst} {w : Scc.IR.Operand} {ra : Int64} :
    ((bodyBlks cx 0 is [w]).all fun x =>
      blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat (4 * x.1)) ra x.2) =
      bodyPhOk okPc ph (fun _ => false) lab cx l is [w] ra := rfl

/-- A resolved label's `labC` is its address under any map agreeing with
the code labels. -/
theorem labC_eq {lo : Nat} {prog : Program} {lab : Label → Int64}
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a) {l : String}
    (hr : (codeOf lo prog l).isSome = true) : labC lo prog l = lab l := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hr
  rw [labC, ha, hlab l a ha]; rfl

/-- `blkPh` at the code labels is `blkPh` at `lab`, every label it reads
resolving. -/
theorem blkPh_labC {lo : Nat} {prog : Program} {lab : Label → Int64}
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool} {ph : Nat → Nat}
    {dead : Nat → Bool} {pc ra : Int64} {blk : List Directive}
    (hr : (blkLabs blk).all (fun l => (codeOf lo prog l).isSome) = true) :
    blkPh okPc ph dead (labC lo prog) pc ra blk = blkPh okPc ph dead lab pc ra blk :=
  blkPh_congr fun L hL => labC_eq hlab (List.all_eq_true.mp hr L hL)

/-- **One function's check gives its premises** at `lab`: the prologue's
`ProPh`, with an instruction the local overflow block's `blkPh`, and the
body's `bodyPhOk`. -/
theorem fnPh1_sound {okPc : Nat → Bool} {ph : Nat → Nat} {lo : Nat} {prog : Program}
    {lab : Label → Int64} (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {cx : FnCtx} {fn : String} {is : List Scc.IR.Inst} {w : Scc.IR.Operand} {ra : Int64}
    (h : fnPh1 okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx fn is w ra = true) :
    ProPh okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [] ∧
      (is ≠ [] → blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        ovfBlk = true) ∧
      bodyPhOk okPc ph (fun _ => false) lab cx (cx.prefix ++ "0_entry") is [w] ra = true := by
  unfold fnPh1 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_rfn, rsc⟩, ren⟩, rpro⟩, rbody⟩, hpro⟩, hovf⟩, hbody⟩ := h
  have hpr := List.all_eq_true.mp rpro
  have e := fun (blk : List Directive) (hsub : ∀ L ∈ blkLabs blk, L ∈ proLabs (Int64.ofInt cx.frame) (proL cx) []) =>
    (List.all_eq_true.mpr fun L hL => hpr L (hsub L hL) :
      (blkLabs blk).all (fun l => (codeOf lo prog l).isSome) = true)
  refine ⟨?_, ?_, ?_⟩
  · apply proPh_of_proPhOk
    simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at hpro ⊢
    rw [labC_eq hlab rsc] at hpro
    obtain ⟨⟨⟨⟨hd, ld1⟩, ld2⟩, br⟩, frr⟩ := hpro
    refine ⟨⟨⟨⟨?_, ld1⟩, ld2⟩, ?_⟩, ?_⟩
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact hd
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact br
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact frr
  · intro hne
    simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true] at hovf
    obtain ⟨⟨rab, rlb⟩, hb⟩ := hovf.resolve_left hne
    rw [labC_eq hlab rab, blkPh_labC hlab rlb] at hb
    exact hb
  · unfold bodyPhOk
    rw [List.all_eq_true] at hbody rbody ⊢
    intro x hx
    have := hbody x hx
    rw [labC_eq hlab ren, blkPh_labC hlab (rbody x hx)] at this
    exact this

open Scc.Cert.PlaceOK.A64 in
/-- **The user functions' phase premises from `PlaceOK`**: at a `func0`
block of a placed output (the `fi`th function of its IR), its prologue's
`ProPh`, with an instruction its local overflow block's `blkPh` (the
abort path's `Local.lb` at `abort_overflow`: `hab_of`'s `hphA`), and its
body's `bodyPhOk`, at A6's `okPcOf`/`phOf`, any label map
agreeing with the code labels (`hlab`), the return address after
`scc_rt_main`'s `bl`. -/
theorem userPh_of_placeOK {cfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt cfg Λ o = true)
    {ir : Scc.IR.Program} (hir : o.place.ir = some ir) {lab : Label → Int64}
    (hlab : ∀ l a, codeOf Λ.code.lo o.prog l = some a → lab l = Int64.ofNat a)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} {fi : Nat} (hf : (Scc.Lower.Inv.func0 name r, fi) ∈ ir.funcs.zipIdx)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    let c := fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir argRegs.length) fi (Scc.Lower.Inv.func0 name r)
    let okPc := Scc.Cert.Rt.A64.okPcOf Λ.code.lo o.prog Λ
    let ph := Scc.Cert.Rt.A64.phOf Λ.code.lo o.prog
    ProPh okPc ph lab (c.local "stack_check") (Int64.ofInt c.frame) (proL c) [] ∧
      (r.insts ≠ [] → blkPh okPc ph (fun _ => false) lab (lab (c.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        Spike.Lib.A64.Abort.Local.lb = true) ∧
      bodyPhOk okPc ph (fun _ => false) lab c (c.prefix ++ "0_entry") r.insts r.ret (lab raL + 4) = true := by
  intro c okPc ph
  obtain ⟨hra, hall⟩ := fnPhOk_parts (fnPh_of_placeOKAt h hir)
  have h1 := fnPhAll_func0 hall hf hI hw
  rw [labC_eq hlab hra] at h1
  rw [hw, ← ovfBlk_eq_lb]
  exact fnPh1_sound hlab h1

end Spike.Lib.LowerA64
