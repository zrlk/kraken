/-
**wc_main's segment end as `MainSeg`** (wake.w, AArch64): the state
at main's `clone` that the pre-spawn segment leaves (`ClonePost`: the end
of `WakeWc.wake_wc_mid_hatW` with the caller's saved pair, main's stack and
the thread pointer's value), and from it with `ClonePre` the pieces of
`WakeMainHRD.hMainR_ofD`'s open `hpc` (`MainSeg`, `hA`, `hZ`).

- `ClonePost L endPc J t s c`: at the clone's `svc` (`wcNS`, and main's
  parent node `JS` in the region `⟨R.base, -96, 16⟩`), the saved pair the
  one `scc_rt_main`'s call of `wc_main` left (`FrG` at `wJ0 (wNC lab J)`),
  `sp` 128 below stack 0's top, the thread pointer `pinA + 8`.
- `hra_of_frG`: the saved return address is `scc_rt_main`'s `.sp0`.
- `hA_of_clone`: `c`'s label is placed at the cell `x9` holds (`ClonePre`'s
  `ValRep`).
- `hZ_of`: main's `x9` slot (`R.addr (-32)`) above stack 0's guard page.
- `mainSeg_of`: `MainSeg`, `hA` and `hZ` at the clone state.
- `hpc_of`: `hMainR_ofD`'s `hpc` from `ClonePost` at every `PreR`.
-/
import Spike.Lib.WakeMainHRD
import Spike.Lib.A64WakeWcMain

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range Marks Entry)
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.WakeA64 Spike.Lib.Handover
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh.WcSp4 (wcNS)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.MainPost (mainSp0)
open Spike.Lib.WakePreA (cloneAt ClonePre)
open Spike.Lib.WakeSpawnR (PreR endR QG ιR)
open Spike.Lib.WakeMainHRD (MainSeg)

/-- **The state at main's `clone`** that the pre-spawn segment leaves: the
end of `wake_wc_mid_hatW` (`wcNS` in `wc_main`'s region `R`, main's parent
node in `⟨R.base, -96, 16⟩`, `R`'s base 80 above `sp`) with its saved pair
`fr` the one `scc_rt_main`'s call left (`FrG` at `wJ0 (wNC lab J) σC`),
`sp` 128 below stack 0's top (`scc_rt_main`'s 48 bytes and `wc_main`'s 80
on the stack the start switches to) and the thread pointer `pinA + 8`. -/
def ClonePost (L : RuntimeLayout) (endPc : Int64) (J : AS → Ctl → Prop) (t : UInt64) (s : State) (c : Ctl) :
    Prop :=
  ∃ (R : Region) (F₂ : MachineData → Prop) (σC : AS) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64),
    R.base.toNat % 16 = 0 ∧ FrG (WakeM.wJ0 (WakeM.wNC (_root_.Executable.labels L.exe).label J).J σC) fr ∧
    At L.exe endPc R F₂ (wcNS (_root_.Executable.labels L.exe).label c (t2 (_root_.Executable.labels L.exe).label)
      (kOf (_root_.Executable.labels L.exe).label) cA m fr) s c ∧
    (⟨R.base, -96, 16⟩ : Region).OK ∧
    At L.exe endPc ⟨R.base, -96, 16⟩ F₂ ⟨cloneAt pfxM L.exe, oP, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
    (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 80 ∧
    s.st.1.regs.SP.toNat + 128 = L.stacksA.toNat + 16384 ∧ t.toBitVec = L.pinA + 0#64 + 8#64

/-- **The saved return address is `scc_rt_main`'s `.sp0`**: `wc_main`'s
entry is `scc_rt_main`'s call node (`wNC`, `x30 = .sp0`), entered without
a register change (`enter`). -/
theorem hra_of_frG {lab : Label → Int64} {J : AS → Ctl → Prop} {σC : AS} {fr : BitVec 64 × BitVec 64}
    (h : FrG (WakeM.wJ0 (WakeM.wNC lab J).J σC) fr) : Int64.ofBitVec fr.2 = lab mainSp0 := by
  obtain ⟨σe, c, ⟨rfl, -, -, h30⟩, rfl⟩ := h
  show Int64.ofBitVec σC.regs.X30.toBitVec = _
  rw [h30]; rfl

/-- **`c`'s label is placed at the cell `x9` holds** at the clone:
`ClonePre`'s `ValRep` of `c`'s locative at its `x9`, `c` bound in main's
source thread to the locative of `l`. -/
theorem hA_of_clone {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {d : Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2}
    {th0 : TermRun.TTh} {l : WeakMem.AllocLabel} {cA : BitVec 64}
    (hC : ClonePre pfx Λ r0 r1 X lbl d s) (hs : s.ths = #[th0])
    (hc : TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (ht : d.1.threads = #[th]) (h9 : th.st.st.1.regs.X9.toBitVec = cA) : lbl l = some cA.toNat := by
  obtain ⟨th', th0', -, cA', -, l', ht', hs', -, -, -, -, -, -, h9', -, -, -, -, -, -, -, -, -, -, -, hc', -, -,
    hv, -⟩ := hC
  rw [ht] at ht'
  obtain rfl : th = th' := by simpa using ht'
  rw [hs] at hs'
  obtain rfl : th0 = th0' := by simpa using hs'
  rw [hc] at hc'
  have e := congrArg (fun w : TermRun.Word => w.val) (by simpa using hc')
  obtain rfl : l = l' := by simpa [Promises.TVal.mk0] using e
  obtain ⟨-, x, hx, rfl⟩ := hv
  simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [Nat.mul_zero, Nat.add_zero] at h9'
  rw [hy, ← h9, ← h9']; rfl

/-- **Main's `x9` slot is above stack 0's guard page**: `R.addr (-32)` is
`sp + 48`, and `sp` is 128 below stack 0's top. -/
theorem hZ_of {L : RuntimeLayout} {Rb : BitVec 64} {sp : Nat} (hb : (Rb.toNat : Int) = sp + 80)
    (hs : sp + 128 = L.stacksA.toNat + 16384) :
    L.stacksA.toNat + 4096 ≤ ((⟨Rb, -96, 16⟩ : Region).addr (-32)).toNat := by
  unfold Region.addr
  have hlt := Rb.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofInt]
  have e : ((-32 : Int) % (2 ^ 64 : Nat)).toNat = 2 ^ 64 - 32 := by decide
  simp only [e]
  omega

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`MainSeg`, `hA` and `hZ` at the clone state** from `ClonePost` and
`ClonePre` (`c`'s label from main's source thread, `hc`). -/
theorem mainSeg_of {th : Thread isaLSE2} {c : Ctl} {J : AS → Ctl → Prop} {t : UInt64}
    (h : ClonePost (RuntimeLayout.ofPlaceW hp i) (endR hp i) J t th.st c)
    {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {d : Cfg} {s : TermRun.Cfg}
    {th0 : TermRun.TTh} {l : WeakMem.AllocLabel}
    (hC : ClonePre pfxM (RuntimeLayout.ofPlaceW hp i).Λ r0 r1 X lbl d s) (hs : s.ths = #[th0])
    (hc : TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (ht : d.1.threads = #[th]) :
    ∃ Rm F₂ cA x29 ra tp, MainSeg hp i th c Rm F₂ cA x29 ra tp ∧ lbl l = some cA.toNat ∧
      (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -96, 16⟩ : Region).addr (-32)).toNat := by
  obtain ⟨R, F₂, σC, cA, m, fr, hal, hfr, hS, hok, hat, hb, hsp, htp⟩ := h
  obtain ⟨-, -, -, -, σ, hA, -, -, -, -, -, -, -, -, h9, -⟩ := hS
  refine ⟨R, F₂, cA, fr.1, fr.2, t.toBitVec, ⟨hat, hb, hok, hal, htp, hra_of_frG hfr⟩,
    hA_of_clone hC hs hc ht ?_, hZ_of hb hsp⟩
  rw [hA.regs]; exact h9

/-- **`hMainR_ofD`'s `hpc` from `ClonePost`**: at every `PreR`, main's
thread at the clone in `ClonePost` at main's control there (`hpost`). -/
theorem hpc_of {asm : String} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range}
    (hpost : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      Spike.Lib.WakeSpawn.SpawnPrem (QG hp i arch R1 μ M r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E 0 d s th
        stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c J t, ClonePost (RuntimeLayout.ofPlaceW hp i) (endR hp i) J t th.st c) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      Spike.Lib.WakeSpawn.SpawnPrem (QG hp i arch R1 μ M r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E 0 d s th
        stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA x29 ra tp, MainSeg hp i th c Rm F₂ cA x29 ra tp ∧ lbl l = some cA.toNat ∧
        (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -96, 16⟩ : Region).addr (-32)).toNat := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q hP hrun hR
  obtain ⟨c, J, t, h⟩ := hpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  obtain ⟨th0, hs, hc⟩ := hR.hc
  exact ⟨c, mainSeg_of hp i h hR.clone hs hc hR.pre.threads⟩

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.mainSeg_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.mainSeg_of

/-- info: 'Spike.Lib.A64.Flow.WakeWc.hpc_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.hpc_of
