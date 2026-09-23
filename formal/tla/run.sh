#!/usr/bin/env bash
# Model-check every TLA+ configuration in formal/tla with TLC.
#
#   ./run.sh                      all configurations expected to PASS
#   ./run.sh --expected-failures  configurations that are EXPECTED to report
#                                 a violation (the permutation-economy
#                                 findings); succeeds iff each one reports
#                                 exactly the expected invariant violation
#   ./run.sh --witnesses          non-vacuity checks: every NoW_* predicate
#                                 (claiming some interesting situation is
#                                 unreachable) must be REFUTED by TLC
#   ./run.sh --all                all three of the above
#   ./run.sh CONFIG...            only the named configurations (basename
#                                 without .cfg), in whichever group they are
#
# Environment:
#   JAVA       java executable            (default: java on PATH)
#   TLA2TOOLS  path to tla2tools.jar      (default: ~/.local/share/tlaplus/tla2tools.jar)
#   WORKERS    TLC worker threads         (default: auto)
#   JAVA_OPTS  extra JVM options          (default: -XX:+UseParallelGC -Xmx8g)
#
# TLC runs in a temporary copy of this directory with a temporary -metadir,
# so no states/ directories or trace files are ever written into the
# repository.  The script also re-runs the PlusCal translator on a copy of
# each PlusCal module and fails if the committed translation is stale.
set -u

HERE=$(cd "$(dirname "$0")" && pwd)
JAVA=${JAVA:-java}
TLA2TOOLS=${TLA2TOOLS:-$HOME/.local/share/tlaplus/tla2tools.jar}
WORKERS=${WORKERS:-auto}
JAVA_OPTS=${JAVA_OPTS:--XX:+UseParallelGC -Xmx8g}

# module:config for configurations that must pass.
PASS_CONFIGS="
Sponge:Sponge_rate2
Sponge:Sponge_rate2_tagged
Sponge:Sponge_rate3
Sponge:Sponge_rate8
Sponge:Sponge_concurrent
Sponge:Sponge_lazy
Sponge:Sponge_lazy_rate8
AeadDecrypt:AeadDecrypt_tag2
AeadDecrypt:AeadDecrypt_tag3
"
# module:config:invariant for configurations that must FAIL with exactly
# that invariant violated (documented findings, see README.md).
EXPECTED_FAILURES="
Sponge:Sponge_economy_get:HashGetMinimal
Sponge:Sponge_economy_squeeze:PermMinimal
"
# module:base-config:witness -- witness must be violated (situation reached)
WITNESSES="
Sponge:Sponge_rate2:NoW_FillBlockTail
Sponge:Sponge_rate3:NoW_FillBlockTail
Sponge:Sponge_rate8:NoW_FillBlockTail
Sponge:Sponge_rate2:NoW_FullPaddingBlock
Sponge:Sponge_rate8:NoW_FullPaddingBlock
Sponge:Sponge_rate2:NoW_SqueezeAtBoundary
Sponge:Sponge_lazy:NoW_SqueezeAtBoundary
Sponge:Sponge_rate2:NoW_SqueezeCrossing
Sponge:Sponge_rate8:NoW_SqueezeCrossing
Sponge:Sponge_rate2_tagged:NoW_Concat
Sponge:Sponge_lazy:NoW_Concat
Sponge:Sponge_rate2:NoW_ZeroSqueeze
Sponge:Sponge_rate2:NoW_AbsorbAfterReinit
Sponge:Sponge_rate2:NoW_Branching
Sponge:Sponge_concurrent:NoW_ConcurrentSharedInput
Sponge:Sponge_concurrent:NoW_CrossDomainHandoff
AeadDecrypt:AeadDecrypt_tag2:NoW_OkMultiBlockTailA
AeadDecrypt:AeadDecrypt_tag2:NoW_OkTailB
AeadDecrypt:AeadDecrypt_tag2:NoW_AuthFailureNonEmpty
AeadDecrypt:AeadDecrypt_tag2:NoW_BadTagLength
AeadDecrypt:AeadDecrypt_tag2:NoW_CombinedOk
AeadDecrypt:AeadDecrypt_tag2:NoW_CombinedShort
AeadDecrypt:AeadDecrypt_tag2:NoW_CtEqualTrue
AeadDecrypt:AeadDecrypt_tag2:NoW_CtEqualLateDiff
AeadDecrypt:AeadDecrypt_tag3:NoW_OkMultiBlockTailA
AeadDecrypt:AeadDecrypt_tag3:NoW_CombinedOk
"
PLUSCAL_MODULES="Sponge AeadDecrypt"

if [ ! -f "$TLA2TOOLS" ]; then
    echo "run.sh: tla2tools.jar not found at $TLA2TOOLS (set TLA2TOOLS)" >&2
    exit 2
fi
if ! "$JAVA" -version >/dev/null 2>&1; then
    echo "run.sh: cannot run java ($JAVA); set JAVA" >&2
    exit 2
fi

mode=pass
selected=""
for arg in "$@"; do
    case "$arg" in
        --expected-failures) mode=fail ;;
        --witnesses) mode=witness ;;
        --all) mode=all ;;
        -h|--help) sed -n '2,28p' "$0"; exit 0 ;;
        -*) echo "run.sh: unknown option $arg" >&2; exit 2 ;;
        *) selected="$selected ${arg%.cfg}" ;;
    esac
done

WORK=$(mktemp -d "${TMPDIR:-/tmp}/formal-tla.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
cp "$HERE"/*.tla "$HERE"/*.cfg "$WORK"/

failures=0

wanted() {
    [ -z "$selected" ] && return 0
    for s in $selected; do [ "$s" = "$1" ] && return 0; done
    return 1
}

check_translation() {
    local mod=$1 dir="$WORK/pcal-$1"
    mkdir -p "$dir"
    cp "$HERE/$mod.tla" "$dir/"
    if ! (cd "$dir" && "$JAVA" -cp "$TLA2TOOLS" pcal.trans -nocfg "$mod.tla" >"$dir/log" 2>&1); then
        echo "FAIL  $mod: PlusCal translation failed"; cat "$dir/log"; return 1
    fi
    if ! cmp -s "$HERE/$mod.tla" "$dir/$mod.tla"; then
        echo "FAIL  $mod: committed TLA+ translation is stale (run pcal.trans -nocfg $mod.tla)"
        diff "$HERE/$mod.tla" "$dir/$mod.tla" | head -20
        return 1
    fi
    echo "ok    $mod: PlusCal translation is up to date"
}

# run_tlc module config -> sets $log, returns TLC's exit status
run_tlc() {
    local mod=$1 cfg=$2
    log="$WORK/$cfg.log"
    # shellcheck disable=SC2086
    mkdir -p "$WORK/jtmp-$cfg"
    (cd "$WORK" && "$JAVA" $JAVA_OPTS -Djava.io.tmpdir="$WORK/jtmp-$cfg" -cp "$TLA2TOOLS" tlc2.TLC \
        -workers "$WORKERS" -deadlock -cleanup -metadir "$WORK/meta-$cfg" \
        -config "$cfg.cfg" "$mod.tla" >"$log" 2>&1)
}

# One line per state of a counterexample: action, pc, and the permutation /
# offset bookkeeping of domain d1 (Sponge) -- enough to read the finding.
compact_trace() {
    awk '
        /^State [0-9]+:/ { if (line != "") print line; n = $2; sub(":", "", n);
                           act = $3; gsub(/[<>]/, "", act); line = "      " n " " act; next }
        /^\/\\ (nperm|offset|written) = / { v = $0; sub(/^\/\\ /, "", v);
                           gsub(/\(d1 :> |\)/, "", v); line = line "  " v }
        END { if (line != "") print line }' "$1"
}

summary() {
    grep -E "^[0-9]+ states generated, [0-9]+ distinct states found, 0 states left|depth of the complete state graph|^Finished in" "$1" \
        | sed 's/^/      /'
}

if [ -z "$selected" ]; then
    for m in $PLUSCAL_MODULES; do
        check_translation "$m" || failures=$((failures + 1))
    done
fi

if [ "$mode" = pass ] || [ "$mode" = all ] || [ -n "$selected" ]; then
    for entry in $PASS_CONFIGS; do
        mod=${entry%%:*}; cfg=${entry#*:}
        wanted "$cfg" || continue
        [ "$mode" = fail ] && [ -z "$selected" ] && continue
        echo "run   $cfg ($mod)"
        run_tlc "$mod" "$cfg"; status=$?
        if [ $status -eq 0 ] && grep -q "Model checking completed. No error has been found." "$log"; then
            echo "PASS  $cfg"; summary "$log"
        else
            echo "FAIL  $cfg (TLC exit $status)"; tail -60 "$log"
            failures=$((failures + 1))
        fi
    done
fi

if [ "$mode" = fail ] || [ "$mode" = all ] || [ -n "$selected" ]; then
    for entry in $EXPECTED_FAILURES; do
        mod=${entry%%:*}; rest=${entry#*:}; cfg=${rest%%:*}; inv=${rest#*:}
        wanted "$cfg" || continue
        [ "$mode" = pass ] && [ -z "$selected" ] && continue
        echo "run   $cfg ($mod, expected violation of $inv)"
        run_tlc "$mod" "$cfg"; status=$?
        if [ $status -ne 0 ] && grep -q "Invariant $inv is violated" "$log"; then
            echo "XFAIL $cfg: $inv violated as documented; counterexample:"
            compact_trace "$log"
        else
            echo "FAIL  $cfg: expected a violation of $inv (TLC exit $status)"; tail -40 "$log"
            failures=$((failures + 1))
        fi
    done
fi

if [ "$mode" = witness ] || [ "$mode" = all ]; then
    for entry in $WITNESSES; do
        mod=${entry%%:*}; rest=${entry#*:}; base=${rest%%:*}; w=${rest#*:}
        cfg="W_${base}_$w"
        sed '/^INVARIANTS/,$d' "$WORK/$base.cfg" > "$WORK/$cfg.cfg"
        printf 'INVARIANTS\n  %s\n' "$w" >> "$WORK/$cfg.cfg"
        run_tlc "$mod" "$cfg"; status=$?
        if [ $status -ne 0 ] && grep -q "Invariant $w is violated" "$log"; then
            echo "ok    $w reachable in $base ($(grep -c '^State [0-9]*:' "$log")-state witness trace)"
        else
            echo "FAIL  $w NOT refuted in $base: the situation is unreachable (vacuity!)"
            tail -20 "$log"
            failures=$((failures + 1))
        fi
    done
fi

if [ $failures -ne 0 ]; then
    echo "run.sh: $failures failure(s)"
    exit 1
fi
echo "run.sh: all selected checks behaved as expected"
