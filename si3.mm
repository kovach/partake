{turn1} game: ~turn.

{setup} game:
  +player 'P,
  +player 'Q.

{deal} game:
  player P,
  +player-card P 'run,
  +player-card P 'act.

spirit-phase:
  player P,
  ~choose-cards
    [ *player P ].

choose-cards:
  choose 1 (
    player-card .*player C,
    player-card .*player D,
    ).

move:
  *it I, *to T,
  +located I -> T.

{turn} turn:
  ~spirit-phase,
  ~fast-phase,
  ~event-phase,
  ~invader-phase,
  ~slow-phase,
  ~time-passes.
