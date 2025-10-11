(lang dune 3.8)

(name logos-pxl-core)
(version 3.0.0-verified)
(authors "LOGOS PXL Core Team")
(maintainers "security@logos.foundation")
(homepage "https://github.com/ProjectLOGOS/LOGOS_PXL_Core")
(bug-reports "https://github.com/ProjectLOGOS/LOGOS_PXL_Core/issues")
(source (github ProjectLOGOS/LOGOS_PXL_Core))
(license MIT)

(package
 (name logos-pxl-core)
 (synopsis "Mathematically Verified PXL Core Runtime")
 (description "OCaml runtime extracted from formally verified Coq theorems")
 (depends
  (ocaml (>= 4.14))
  (dune (>= 3.8))
  (cohttp-lwt-unix (>= 5.0))
  (lwt (>= 5.6))
  (yojson (>= 2.0))))

(executable
 (name pxl_runtime)
 (public_name pxl-runtime)
 (modules pxl_core pxl_runtime)
 (libraries cohttp-lwt-unix lwt yojson))

(rule
 (target pxl_core.ml)
 (deps ExtractCore.v)
 (action
  (run coqc -Q %{workspace_root}/pxl-minimal-kernel-main/coq PXLs
            -Q %{workspace_root}/modules/IEL/source PXLs.IEL.Source
            ExtractCore.v)))

(rule
 (target pxl_core.mli)
 (deps ExtractCore.v)
 (action
  (run coqc -Q %{workspace_root}/pxl-minimal-kernel-main/coq PXLs
            -Q %{workspace_root}/modules/IEL/source PXLs.IEL.Source
            ExtractCore.v)))