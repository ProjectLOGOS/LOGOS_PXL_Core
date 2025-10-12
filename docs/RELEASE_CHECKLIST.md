# Release Checklist

1. `make verify-kernel`
2. `make docs-index`
3. `make coq-test`
4. Record deterministic kernel hash from `verify-kernel` output.
5. Update `CHANGELOG.md` (if present).
6. Tag and push: `git tag vX.Y.Z && git push --tags`
7. Create GitHub Release and attach `docs/COQ_INDEX.md`.
8. Note tool versions from `toolversions.txt` in the release body.
