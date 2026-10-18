import L6Poly.Basic
import L6Check.Certs.Cfafc3cdcdaca97ae

/-! Cofactor certificates, batch 52: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_fafc3cdcdaca97ae : L6.Poly.checkCert L6.Certs.Cfafc3cdcdaca97ae = true := by native_decide

end L6.Poly.Checks
