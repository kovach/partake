{turn1} game: ~turn.

{setup} game:
  +player 'P,
  +player 'Q.

mk-card:
  +card C,
  +name C .*name,
  +located C -> .deck.

{deal} game:
  +deck D,
  ~mk-card [ *name 'run ],
  ~mk-card [ *name 'act ],
  player P,
  +choose-area P _,
  .

spirit-phase:
  player P,
  ~choose-cards
    [ *player P ].

choose-cards:
  *player P,
  choose 1 (
    card C, name C Name,
    located C -> .deck
  ), ~move [ *it Id, *to P.choose-area ].

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
