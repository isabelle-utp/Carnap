#!/usr/bin/env bash
#
# Regression runner for the carnap-check CLI test proofs.
#
# Every *.carnap file in this directory is a self-describing proof bundle: it
# begins with a `logic <system>` directive, so carnap-check can be invoked with
# just the file path.  A file passes iff carnap-check exits 0 (all lemmas
# proved).
#
# Usage:
#   ./run-tests.sh            # build carnap-check, then run every proof
#   ./run-tests.sh -v         # also echo carnap-check's output for each file
#   ./run-tests.sh a.carnap … # run only the given files (still builds first)
#
# Exit status is 0 iff every proof checked passes.

set -u

# Directory this script lives in, so it works from any CWD.
TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$TESTS_DIR/../../.." && pwd)"

VERBOSE=0
FILES=()
for arg in "$@"; do
    case "$arg" in
        -v|--verbose) VERBOSE=1 ;;
        -h|--help)
            sed -n '2,20p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *) FILES+=("$arg") ;;
    esac
done

# Default to every proof in the tests directory.
if [ "${#FILES[@]}" -eq 0 ]; then
    while IFS= read -r f; do FILES+=("$f"); done \
        < <(find "$TESTS_DIR" -maxdepth 1 -name '*.carnap' | sort)
fi

cd "$REPO_ROOT"

echo "Building Carnap:exe:carnap-check ..."
if ! stack build Carnap:exe:carnap-check; then
    echo "BUILD FAILED" >&2
    exit 1
fi

pass=0
fail=0
failed_files=()

echo
echo "Running ${#FILES[@]} proof(s):"
for f in "${FILES[@]}"; do
    name="$(basename "$f")"
    output="$(stack exec carnap-check -- "$f" 2>&1)"
    status=$?
    if [ "$status" -eq 0 ]; then
        printf '  PASS  %s\n' "$name"
        pass=$((pass + 1))
    else
        printf '  FAIL  %s\n' "$name"
        fail=$((fail + 1))
        failed_files+=("$name")
    fi
    if [ "$VERBOSE" -eq 1 ]; then
        printf '%s\n' "$output" | sed 's/^/          /'
    fi
done

echo
echo "Results: $pass passed, $fail failed (of $((pass + fail)))."
if [ "$fail" -ne 0 ]; then
    printf 'Failed: %s\n' "${failed_files[*]}"
    exit 1
fi
exit 0
