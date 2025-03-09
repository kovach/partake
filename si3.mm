game: ~turn.

{setup} game:
  +player 'P,
  +player 'Q.

{deal} game:
  player P,
  +player-card P 'run,
  +player-card P 'act.

spirit-phase:
  player P,
  choose 1 (player-card P C).

{turn} turn:
  ~spirit-phase,
  ~fast-phase,
  ~event-phase,
  ~invader-phase,
  ~slow-phase,
  ~time-passes.
