# Sealed semantic baselines

No baseline has been sealed for this new packaging. Follow
`docs/PUBLISHING.md` after its clean build/audit and Comparator gate.

A committed `<paper>-v<version>.json` records the accepted source commit,
toolchain, export URL and SHA256, comparator configuration SHA256 and endpoint
manifest SHA256. The generated NDJSON environment lives in the release asset,
not this source directory. Do not change a certified baseline in place.
