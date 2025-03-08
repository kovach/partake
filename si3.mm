{start} game: ~turn.

{setup} game:
  +player 'P,
  +player 'Q.

{turn} turn:
  ~spirit-phase,
  ~fast-phase,
  ~event-phase,
  ~invader-phase,
  ~slow-phase,
  ~time-passes.

spirit-phase:
  player P,
  +the-player P,
  ~growth-phase,
  ~energy,
  ~choose-cards.