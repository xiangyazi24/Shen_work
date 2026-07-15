# Remote verification protocol (mini cannot lake build)

All Lean verification happens on uisai2 in a per-line staging dir with warm cache.
Your staging dir is given in your dispatch prompt (e.g. /dev/shm/lean/Shen_work-p2lp).

1. After editing/creating .lean files locally:
   rsync -a ~/repos/Shen_work/ShenWork/ uisai2:<STAGING>/ShenWork/
2. Single-file check (fast):
   ssh uisai2 'cd <STAGING> && env LAKE_NO_UPDATE=1 PATH=$HOME/.elan/bin:$PATH lake env lean ShenWork/<Paper>/<File>.lean'
3. Module build:
   ssh uisai2 'cd <STAGING> && env LAKE_NO_UPDATE=1 PATH=$HOME/.elan/bin:$PATH lake build ShenWork.<Paper>.<Module>'
4. #print axioms: append the directive temporarily, run step 2, read output, REMOVE it.

Never `lake update`. Never git commands (orchestrator commits). Never full-tree build.
Never touch uisai2:~/repos/Shen_work (stale clone, off limits). Only build modules you touch.
