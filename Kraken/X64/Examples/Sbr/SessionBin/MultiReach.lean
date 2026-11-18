import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# More than one element: the session does not depend on `ac->fdsp`'s value

`SReach` carries the value of `ac->fdsp` (`Args.fdsp`) along, but no step reads it: every
clause that mentions it is an equality between the values before and after a call. So setting
it to any `f` in both the start and the end of a run gives a run again (`sreach_setF`), and
init's values with `fdsp := f` are `setF f` of init's values (`σInit_setF`). With this, an
element's own part (`SbrElem`) can be rejoined with the shared cell `ac->fdsp` at whatever value
it holds.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-- The session's values with `ac->fdsp` set to `f`. -/
def setF (f : BitVec 64) (σ : SV) : SV := ({ σ.1 with fdsp := f }, σ.2)

theorem σInit_setF (i : InitIn) (f : BitVec 64) :
    σInit { i with fdsp := f } = setF f (σInit i) := rfl

/-- `ff_aac_sbr_decode_extension`'s step, with `fdsp := f` on both sides. -/
theorem step_dec_setF {id : BitVec 32} {σ : SV} {d : DecExt.DS} (f : BitVec 64)
    (h : DecExt.DecOut Ps.PsInv ⟨σ.1.R, toDS σ, ⟨0, 0, 0⟩, 0, 0, 0, 0⟩ d) :
    Step (.dec id) (setF f σ) (setF f (ofDS d), true) := by
  obtain ⟨hmi, hlc, hok, hpi, ⟨k1, _, k3, k4, k5, k6, k7⟩, hsi⟩ := h
  exact Step.dec (σ := setF f σ) { d with a := { d.a with fdsp := f } }
    ⟨hmi, hlc, hok, hpi, ⟨k1, rfl, k3, k4, k5, k6, k7⟩, hsi⟩

/-- `ff_aac_sbr_decode_usac_data`'s step, with `fdsp := f` on both sides. -/
theorem step_usac_setF {cpe : Bool} {σ σ' : SV} {ok : Bool} (f : BitVec 64)
    (h : Step (.usac cpe) σ (σ', ok)) : Step (.usac cpe) (setF f σ) (setF f σ', ok) := by
  cases h with
  | usac st ret it hmi hlc hk hsp hlb hl =>
    obtain ⟨k1, k2, k3, k4, _, k6, k7, k8⟩ := hk
    exact Step.usac (σ := setF f σ) { st with x := { st.x with fdsp := f } } ret it hmi hlc
      ⟨k1, k2, k3, k4, rfl, k6, k7, k8⟩ hsp hlb hl

/-- `ff_aac_sbr_config_usac`'s step, with `fdsp := f` on both sides. -/
theorem step_config_setF {σ σ' : SV} {ok : Bool} (f : BitVec 64)
    (h : Step .config σ (σ', ok)) : Step .config (setF f σ) (setF f σ', ok) := by
  cases h with
  | config st it hoff hsp hk =>
    obtain ⟨k1, k2, k3, k4, _, k6, k7, k8⟩ := hk
    have hx : st.x = σ.1.turnoff := congrArg Prod.fst hoff
    have hh : st.h = (hidOf σ).turnoff := congrArg Prod.snd hoff
    refine Step.config (σ := setF f σ) { st with x := { st.x with fdsp := f } } it ?_ hsp
      ⟨k1, k2, k3, k4, rfl, k6, k7, k8⟩
    show (({ st.x with fdsp := f } : Args), st.h) = (_, _)
    rw [hx, hh]; rfl

/-- `ff_aac_sbr_apply`'s step, with `fdsp := f` on both sides. -/
theorem step_apply_setF {σ σ' : SV} {ok : Bool} (f : BitVec 64)
    (h : Step .apply σ (σ', ok)) : Step .apply (setF f σ) (setF f σ', ok) := by
  cases h with
  | @apply _ y u hr =>
    obtain ⟨r1, _, r3, r4, r5, r6, r7, r8, r9⟩ := hr
    exact Step.apply (σ := setF f σ) (y := { y with fdsp := f }) u
      ⟨r1, rfl, r3, r4, r5, r6, r7, r8, r9⟩

/-- A frame step, with `fdsp := f` on both sides. -/
theorem step_frame_setF {σ σ' : SV} {ok : Bool} (f : BitVec 64)
    (h : Step .frame σ (σ', ok)) : Step .frame (setF f σ) (setF f σ', ok) := by
  cases h with
  | frame ok hf =>
    have h' := congrArg (fun z : Args => ({ z with fdsp := f } : Args)) hf
    exact Step.frame (σ := setF f σ) ok h'

/-- Every step, with `fdsp := f` on both sides. -/
theorem step_setF {ev : Ev} {σ σ' : SV} {ok : Bool} (f : BitVec 64)
    (h : Step ev σ (σ', ok)) : Step ev (setF f σ) (setF f σ', ok) := by
  cases ev with
  | dec id => cases h with | dec d hd => exact step_dec_setF f hd
  | usac cpe => exact step_usac_setF f h
  | config => exact step_config_setF f h
  | apply => exact step_apply_setF f h
  | frame => exact step_frame_setF f h

/-- **`fdsp` equivariance of `SReach`**: a run with `ac->fdsp` set to `f` at both ends. -/
theorem sreach_setF {σ₀ σ : SV} {ok : Bool} (f : BitVec 64) (h : SReach σ₀ σ ok) :
    SReach (setF f σ₀) (setF f σ) ok := by
  induction h with
  | init => exact SReach.init
  | step ev _ ha hf hs ih => exact SReach.step ev ih ha hf (step_setF f hs)

end Kraken.Examples.Sbr.SessionBin
