VERSION 0.8

# ================ Aeneas (Rust -> Lean verification) ================
# Charon lowers the crate's MIR to LLBC, Aeneas turns LLBC into a pure Lean model, and the
# proofs in verification/ are checked against that model. Everything runs in containers.
#
#   earthly +prove      # charon -> aeneas -> lake build (proofs + axiom audit)
#   earthly +extract    # also writes the generated model under verification/ for editor use
#
# The shipped code is what gets extracted: the raw-pointer word loads and the address tests
# behind the SWAR parsers (`src/load.rs`) are left opaque and modelled by hand, so every
# theorem holds for the little-endian value of the bytes, whichever alignment branch runs.

# Aeneas is a fork (Lean 4.34 backend, iterator and closure fixes); Charon is built at the
# fork's `charon-pin`, so the LLBC producer and the OCaml AST Aeneas is compiled against are
# the same commit. Bump AENEAS_COMMIT and CHARON_PIN together.
ARG --global AENEAS_REPO=https://github.com/gilescope/aeneas
ARG --global AENEAS_COMMIT=fbd149f8693ee58a4bb0f78d447564e9c70496a1
ARG --global CHARON_REPO=https://github.com/gilescope/charon
ARG --global CHARON_PIN=c3baf87fb05a44d6fdc1892b3d4b4ad7b9dd9d3b
# Must match charon/rust-toolchain at CHARON_PIN and backends/lean/lean-toolchain at
# AENEAS_COMMIT; the tools image fails early if either drifts.
ARG --global CHARON_TOOLCHAIN=nightly-2026-09-17
ARG --global LEAN_VERSION=4.34.0
ARG --global LEAN_SHA256_ARM64=40b04fdb7fb849d3c80e10c3bbeebc7b7354b6d3f07450b9168c2149b40d2a82
ARG --global LEAN_SHA256_AMD64=caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b
ARG --global RUSTUP_VERSION=1.28.2
ARG --global RUSTUP_SHA256_ARM64=e3853c5a252fca15252d07cb23a1bdd9377a8c6f3efa01531109281ae47f841c
ARG --global RUSTUP_SHA256_AMD64=20a06e644b0d9bd2fbdbfd52d42540bdde820ea7df86e92e533c073da0cdd43c

# The fork's `aeneas` (OCaml); its Lean backend sources are saved alongside. The pins come
# after the opam install, so bumping them rebuilds only Aeneas.
aeneas-fork:
    FROM ocaml/opam@sha256:bbaac53e502f6602013d8967c3a54cfcb898b556f453ab72e8e23966c3c681df
    ENV LC_ALL=C.UTF-8
    ENV TZ=UTC
    RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends libgmp-dev pkg-config \
        && sudo rm -rf /var/lib/apt/lists/*
    RUN opam install -y calendar core_unix domainslib easy_logging menhir \
          ocamlformat.0.27.0 ocamlgraph odoc ppx_deriving ppx_deriving_yojson \
          progress unionFind visitors yojson zarith logs \
        && opam clean -a -c -s --logs
    WORKDIR /home/opam/aeneas
    RUN git init -q . && git fetch -q --depth 1 "$AENEAS_REPO" "$AENEAS_COMMIT" \
        && git checkout -q FETCH_HEAD \
        && grep -qx "$CHARON_PIN" charon-pin \
        && git init -q charon && git -C charon fetch -q --depth 1 "$CHARON_REPO" "$CHARON_PIN" \
        && git -C charon checkout -q FETCH_HEAD
    RUN cd src && opam exec -- dune build main.exe
    SAVE ARTIFACT src/_build/default/main.exe aeneas
    SAVE ARTIFACT backends/lean lean

# Rust nightly (charon's), charon, Lean and the fork's Aeneas with its backend built.
tools:
    FROM debian:trixie-slim@sha256:a29215f6a35e51e22adffa17f89e9d2ef06214e64a2bad10d765c46aea49f11f
    ARG TARGETARCH
    ENV LC_ALL=C.UTF-8
    ENV TZ=UTC
    RUN apt-get update \
        && apt-get install -y --no-install-recommends ca-certificates curl git gcc libc6-dev libgmp10 zstd \
        && rm -rf /var/lib/apt/lists/*
    # Per-arch names and digests; anything but arm64/amd64 fails loudly.
    RUN case "$TARGETARCH" in \
          arm64) echo "aarch64 linux_aarch64 $RUSTUP_SHA256_ARM64 $LEAN_SHA256_ARM64" ;; \
          amd64) echo "x86_64 linux $RUSTUP_SHA256_AMD64 $LEAN_SHA256_AMD64" ;; \
          *) echo "unsupported TARGETARCH=$TARGETARCH (want arm64 or amd64)" >&2; exit 1 ;; \
        esac > /arch
    ENV RUSTUP_HOME=/opt/rustup
    ENV CARGO_HOME=/opt/cargo
    ENV PATH=/opt/aeneas:/opt/lean/bin:/opt/cargo/bin:$PATH
    RUN read cpu _ sha _ < /arch \
        && curl -fsSLo /tmp/rustup-init "https://static.rust-lang.org/rustup/archive/$RUSTUP_VERSION/$cpu-unknown-linux-gnu/rustup-init" \
        && echo "$sha  /tmp/rustup-init" | sha256sum -c - \
        && chmod +x /tmp/rustup-init \
        && /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain "$CHARON_TOOLCHAIN" \
             --component rustc-dev,llvm-tools,rust-src,miri \
        && rm /tmp/rustup-init \
        && cargo miri setup  # charon's full-MIR std sysroot, built once here
    # RUSTUP_TOOLCHAIN overrides charon's rust-toolchain file, whose cross targets we don't
    # need; it names the same channel (checked first).
    RUN git init -q /tmp/charon \
        && git -C /tmp/charon fetch -q --depth 1 "$CHARON_REPO" "$CHARON_PIN" \
        && git -C /tmp/charon checkout -q FETCH_HEAD \
        && grep -q "channel = \"$CHARON_TOOLCHAIN\"" /tmp/charon/charon/rust-toolchain \
        && cd /tmp/charon/charon \
        && RUSTUP_TOOLCHAIN="$CHARON_TOOLCHAIN" cargo build --release --locked --bin charon --bin charon-driver \
        && mkdir -p /opt/aeneas && cp target/release/charon target/release/charon-driver /opt/aeneas/ \
        && /opt/aeneas/charon version | grep -q "$CHARON_PIN" \
        && rm -rf /tmp/charon /opt/cargo/registry /opt/cargo/git
    RUN read _ asset _ sha < /arch \
        && curl -fsSLo /tmp/lean.tar.zst "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/lean-$LEAN_VERSION-$asset.tar.zst" \
        && echo "$sha  /tmp/lean.tar.zst" | sha256sum -c - \
        && mkdir -p /opt/lean && tar --zstd -xf /tmp/lean.tar.zst -C /opt/lean --strip-components=1 && rm /tmp/lean.tar.zst
    COPY +aeneas-fork/aeneas /opt/aeneas/aeneas
    COPY +aeneas-fork/lean /opt/aeneas/backends/lean
    RUN grep -qx "leanprover/lean4:v$LEAN_VERSION" /opt/aeneas/backends/lean/lean-toolchain
    # The backend against Mathlib's cache, once.
    RUN cd /opt/aeneas/backends/lean && lake exe cache get && lake build Aeneas
    SAVE IMAGE atoi-radix10-aeneas-tools:local

# The crate as LLBC, from the production code: the five `load` wrappers (raw-pointer reads and
# the address test) are opaque, so Aeneas declares them and verification/ models them in
# `FunsExternal.lean` as the little-endian byte fold and an uninterpreted Bool. `IntErrorKind`
# is taken from core's source so the error kinds are the real enum, not a hand model.
llbc:
    FROM +tools
    WORKDIR /src
    COPY Cargo.toml Cargo.lock ./
    # benches/ only because Cargo.toml declares the bench target; it is not extracted.
    COPY --dir src benches ./
    # What to extract. The default is the five SWAR chunk parsers, which the proofs cover. The
    # generic `parse` needs the fork's join of early-exit branches (branch giles-join-early-exit):
    # without it Aeneas duplicates the code after each of its 71 `if`s and runs out of memory.
    # Pass --CHARON_FLAGS='' to extract the whole crate.
    ARG CHARON_FLAGS="--start-from crate::parse_2_chars --start-from crate::parse_4_chars \
        --start-from crate::parse_8_chars --start-from crate::parse_16_chars \
        --start-from crate::parse_32_chars"
    RUN charon cargo --preset=aeneas $CHARON_FLAGS \
          --opaque crate::load::misaligned \
          --opaque crate::load::load_u16 --opaque crate::load::load_u32 \
          --opaque crate::load::load_u64 --opaque crate::load::load_u128 \
          --include core::num::error::IntErrorKind \
          --dest-file atoi_radix10.llbc > charon.log 2>&1 || { cat charon.log; exit 1; }
    SAVE ARTIFACT atoi_radix10.llbc
    SAVE ARTIFACT charon.log AS LOCAL verification/build/charon.log

# The pure Lean model; also written under verification/ for editor use (git-ignored).
extract:
    FROM +tools
    COPY +llbc/atoi_radix10.llbc .
    RUN aeneas -backend lean -dest gen -split-files -gen-lib-entry -no-progress-bar \
          -filter-trait-methods atoi_radix10.llbc > aeneas.log 2>&1 || { cat aeneas.log; exit 1; }
    # Aeneas writes a template only when there is something external; keep the saves total.
    RUN for f in FunsExternal_Template TypesExternal_Template; do \
          [ -f gen/$f.lean ] || echo '-- nothing external' > gen/$f.lean; done
    SAVE ARTIFACT aeneas.log AS LOCAL verification/build/aeneas.log
    SAVE ARTIFACT gen/AtoiRadix10.lean AS LOCAL verification/AtoiRadix10.lean
    SAVE ARTIFACT gen/Types.lean AtoiRadix10/Types.lean AS LOCAL verification/AtoiRadix10/Types.lean
    SAVE ARTIFACT gen/Funs.lean AtoiRadix10/Funs.lean AS LOCAL verification/AtoiRadix10/Funs.lean
    SAVE ARTIFACT gen/FunsExternal_Template.lean AtoiRadix10/FunsExternal_Template.lean \
        AS LOCAL verification/AtoiRadix10/FunsExternal_Template.lean
    SAVE ARTIFACT gen/TypesExternal_Template.lean AtoiRadix10/TypesExternal_Template.lean \
        AS LOCAL verification/AtoiRadix10/TypesExternal_Template.lean

# Re-resolves verification/'s Lake manifest against the tools image's backend; run after
# bumping AENEAS_COMMIT.
lock:
    FROM +tools
    WORKDIR /proofs
    COPY verification/lakefile.lean verification/lean-toolchain ./
    RUN lake update
    SAVE ARTIFACT lake-manifest.json AS LOCAL verification/lake-manifest.json

# Checks the proofs: the generated model, the hand-written externals, the specs, and the
# axiom audit. Warnings are errors in our modules (`strict` in the lakefile).
prove:
    FROM +tools
    WORKDIR /proofs
    COPY verification/lakefile.lean verification/lake-manifest.json verification/lean-toolchain ./
    RUN lake exe cache get
    COPY +extract/AtoiRadix10.lean ./
    COPY +extract/AtoiRadix10 ./AtoiRadix10
    COPY verification/AtoiRadix10/FunsExternal.lean verification/AtoiRadix10/TypesExternal.lean ./AtoiRadix10/
    COPY verification/Proofs.lean verification/Audit.lean ./
    COPY --dir verification/Proofs ./
    RUN lake build

# Where Aeneas spends its memory on the LLBC: trace the interpreter under a virtual-memory
# cap (kB) so an explosion dies in minutes, and keep the tail of the trace.
#   earthly +diagnose --CHARON_FLAGS='--start-from crate::parse ...' --LOGGERS=Interp
diagnose:
    FROM +tools
    ARG LOGGERS=Interp
    ARG ULIMIT_KB=8000000
    COPY +llbc/atoi_radix10.llbc .
    RUN aeneas -help 2>&1 | grep -o 'existing loggers are: {[^}]*}' | head -1 > diag.log; \
        (ulimit -v $ULIMIT_KB; aeneas -backend lean -dest gen -sequential -no-progress-bar \
          -log $LOGGERS atoi_radix10.llbc 2>&1; echo "aeneas exit=$?") | tail -c 400000 >> diag.log
    SAVE ARTIFACT diag.log AS LOCAL verification/build/aeneas-diag.log
