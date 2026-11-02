/-
**hello's owned runtime words are off the root's arena** (x86-64; `offH_own` of the twin of
`Spike/Lib/A64HelloHrdArena.lean`, stated on its own so that the callee's fence (`Ti2OffW`) need not wait on the
root's arena premises): at the root's layout `RuntimeLayout.ofPlaceWX hpw (immsH Λ0 i0)` and arena `arW`, the four
runtime counters `scc_rt_pinned_next`, the stack lock, the free count and the cursor, and `scc_rt_nthreads`, are off
the arena's cells and are not its counter word.

- `offW_arWH`: every runtime word is off `arW` (in `.data` or `pinned`, apart from the counter by A8's `ctrSep`).
- `offH_own`: the owned words (the four counters and `scc_rt_nthreads`) are off `arW`.

Unlike AArch64, the runtime words' case is x86-64 wake's `CalWf.off_of` at a word of `rtWords` (AArch64:
`StartH0Ti.offW_arW`), `scc_rt_nthreads`'s is `CalWf.hoffN_W`, over `PlaceWX` and `ofPlaceWX`.
-/
import Spike.Lib.X64WakeWfCalOff
import Spike.Lib.X64HelloImms

namespace Spike.Lib.X64.HelloPh.HrdArena

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0`. -/
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

/-- **A runtime word is off the root's arena** and not its counter word: in `.data` or `pinned` (`words_mapped`),
apart from the counter (A8's `ctrSep`). -/
theorem offW_arWH : ∀ w ∈ (Ly).rtWords, ¬ ((AR).heap ≤ w.toNat ∧ w.toNat < (AR).heap + 16 * (AR).cells) ∧
    (⟨w, 8⟩ : Loc) ≠ (AR).ctrLoc := fun w hw =>
  Spike.Lib.X64.WakePh.CalWf.off_of hpw IH (by simpa using ((Ly).words_mapped _ hw).2.2 0 (by decide))
    (Spike.Lib.X64.WakePh.CalWf.ne_of_sep
      (Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX IH hpw) _ hw))

/-- **The owned words are off `arW`'s cells and its counter**: the four counters (`offW_arWH`) and
`scc_rt_nthreads` (`CalWf.hoffN_W`). -/
theorem offH_own (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ w', (w' = (Ly).pnA ∨ w' = (Ly).lockA ∨ w' = (Ly).freeNA ∨ w' = (Ly).nextA ∨ w' = NT) →
      ¬ ((AR).heap ≤ w'.toNat ∧ w'.toNat < (AR).heap + 16 * (AR).cells) ∧ w' ≠ BitVec.ofNat 64 (AR).ctr :=
  fun w' hw' => by
    have hof : ¬ ((AR).heap ≤ w'.toNat ∧ w'.toNat < (AR).heap + 16 * (AR).cells) ∧
        (⟨w', 8⟩ : Loc) ≠ (AR).ctrLoc := by
      rcases hw' with rfl | rfl | rfl | rfl | rfl
      · exact offW_arWH hpw i0 _ (Ly).pn_mem
      · exact offW_arWH hpw i0 _ (Ly).lock_mem
      · exact offW_arWH hpw i0 _ (Ly).freeN_mem
      · exact offW_arWH hpw i0 _ (Ly).next_mem
      · exact Spike.Lib.X64.WakePh.CalWf.hoffN_W hpw IH hA13
    exact ⟨hof.1, fun h => hof.2 (by rw [h]; rfl)⟩

end Spike.Lib.X64.HelloPh.HrdArena

/-- info: 'Spike.Lib.X64.HelloPh.HrdArena.offH_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdArena.offH_own
