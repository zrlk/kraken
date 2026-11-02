/-
**The threads abort path holds both TCB self words, at hello's level 2** (x86-64 only; the `ownGHXW` companion of
`Spike/Lib/X64HelloRefAb.lean`, the hello counterpart of wake's `X64WakeRefLft`): on the refusal's threads abort
path below main's frame (`RefO.TOblH`'s region `R.callee (-136 - 8) (-24) 16`), entered from `.spawnfail5`'s
`call` (the return address `.Lwc_main.x27`), main holds both words: `tcbM` (on the pool from `.x1` on,
`selfOwnH`) and `tcbWH` (in `scc_rt_abort`'s code with the return address `.x27`, `selfOwnWH`), and no
instruction of the path writes memory (wake's `tpathW_noW`). So both appended maps may be appended at every node
(`CstOkH`), which lifts the path's `W2H` to `Wcl2X.W2HX`.

- `bandIn_preH`: the dispatcher's band `[-32, 8]` of the callee's region lies in the first stack, from `PreH`'s
  region (its base `96` below stack 0's top).
- `cst_x27H`: `CstH L (tM L) (tWH L)` on the path from `.x27` in a band on the pool.
- `refCstH`: `CstOkH` at every node of the path, in `TOblH`'s shape.

No absolute address appears in a statement here.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against wake's `RefLft`: the return address is
`.Lwc_main.x27` (wake `.x23`), the worker's word `tcbWH L` (`pinA + 112`; wake `tcb2`), the classes are
`OwnCstX`'s (`CstH`, `cstOkH_of`), the callee's region is at `-144` below main's 128-byte frame (wake `-80`), and
the conclusion is the pointwise `CstOkH` (wake's `Lft2`, the lift itself) so that the lift is `w2HX_of`.
-/
import Spike.Lib.X64HelloRefAb
import Spike.Lib.X64HelloOwnCstX
import Spike.Lib.X64WakeRefLft

namespace Spike.Lib.X64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64.WakePh (inPc AbP BandIn spPool_of_band raAt_iff tcbM tM)
open Spike.Lib.X64.HelloPh (lo CstH CstOkH selfOwnH_iffC ownSH_of_self ownSWH_of_self cstOkH_of tWH)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (helloCells)

variable {L : RuntimeLayout}

/-- **The dispatcher's band on the first stack** from `PreH`'s region: `R.base + 96` at the first stack's top,
the callee's `[-32, 8]` at `R`'s `[-176, -136]`. -/
theorem bandIn_preH {R : Region} (hR : R.OK) (hlo : R.lo ≤ -384) (hhi : 16 ≤ R.hi)
    (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) : BandIn L (R.callee (-136 - 8) (-24) 16) := by
  intro k h1 h2
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  simp only at hs1 hs2
  have he : (R.callee (-136 - 8) (-24) 16).addr k = R.addr (-136 - 8 + k) := by
    simp only [Region.callee, Region.addr_add]; rfl
  rw [he]
  have e := Region.addr_toNat_of hR (k := -136 - 8 + k) (by omega) (by omega)
  omega

/-- **Both TCB words on the path from `.x27`** in a band on the pool: `selfOwnH` (on the pool, `scc_rt_abort`
above `.x1`) and `selfOwnWH` (in `scc_rt_abort`'s code with the return address `.x27`). -/
theorem cst_x27H (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {R : Region} (hb : BandIn L R) {s : State} (h : AbP L R (L.lab ".Lwc_main.x27").toBitVec s) :
    CstH L (tM L) (tWH L) s := by
  have eA : L.lab "scc_rt_abort" = Int64.ofNat 4202486 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have eW : L.lab "scc_rt_thr_worker" = Int64.ofNat 4202972 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hin := h.1
  unfold inPc at hin
  rw [eA, eW] at hin
  have hA : (Int64.ofNat 4202486).toBitVec.toNat = 4202486 := by decide
  have hW' : (Int64.ofNat 4202972).toBitVec.toNat = 4202972 := by decide
  rw [hA, hW'] at hin
  exact ⟨ownSH_of_self ((selfOwnH_iffC hlab).mpr (.inl ⟨spPool_of_band hb h.2.2.2, by omega⟩)),
    ownSWH_of_self (.inr (.inr ⟨h.1, (raAt_iff h _).2 rfl⟩))⟩

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)

include hp hlo hlab in
/-- **`CstOkH` at every node of the refusal's threads abort path** (wake's `tpathW_lft2` at `CstOkH`): `AbP`
there and at the successors (`abPT_x27H`), no write (wake's `tpathW_noW`), both words at every `AbP` state
(`cst_x27H`, the band from `PreH`), `tcbM` off `ownGH`'s words (`hs`, `ha`) and `tcbWH` off `ownGHX`'s (`hW`). -/
theorem refCstH (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ ntA L.lab)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab]) (lbl : Lbl) (l : WeakMem.AllocLabel)
    (ws : List TermRun.Word) :
    TOblH L lbl l ws (fun _ s _ => CstOkH (Spike.Lib.X64.PhRec.μ L) L (ntA L.lab) s) (fun _ _ => False) := by
  intro R m0 cP sl cA me m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_ofPreH hpre
  obtain ⟨-, -, -, -, hR, -, hRlo, hRhi, hbase⟩ := hpre
  have hb := bandIn_preH hR hRlo hRhi hbase
  have hlays : Scc.Cert.Rt.X64.Lays L.exe helloCells L.pfx := hp ▸ L.lays
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hd := Scc.Cert.Rt.X64.Abort.code_disp (c0 := c0) hlays (hendH hp) hsd.2
  have hst := Scc.Cert.Rt.X64.Abort.code_stubs (c0 := c0) hlays (hendH hp) SccCode.hello_abort .threads
  rw [raT_x27H hlab]
  exact TPathW.mapWK (TPathW.and (TPathW.ofAbPT (abPT_x27H hp hlo hlab (c0 := c0) rfl hR' hlo' hhi'))
    (Spike.Lib.X64.WakePh.tpathW_noW (ra := (L.lab ".Lwc_main.x27").toBitVec) hR' hlo' hhi' hd hst)
    fun s c h₁ h₂ => And.intro h₁ h₂) fun s _ hw _ =>
    ⟨cstOkH_of hs ha hW (cst_x27H hlab hb hw.1.1) (fun s' hs' => cst_x27H hlab hb (hw.1.2 s' hs'))
      (fun hns tree he => hw.2 hns tree he _), fun _ h => h⟩

end Spike.Lib.X64.HelloPh.RefO

/-- info: 'Spike.Lib.X64.HelloPh.RefO.bandIn_preH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.bandIn_preH

/-- info: 'Spike.Lib.X64.HelloPh.RefO.cst_x27H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.cst_x27H

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refCstH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refCstH
