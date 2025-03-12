{turn1} game: ~turn [ *count 1].
{setup} game:
  +player 'P,
  +dahan D,
  +located D -> 1,
  .

{deal} game:
  +deck D,
  ~mk-card [ *name 'instruments ],
  ~mk-card [ *name 'call-to-isolation ],
  player P,
  +choose-area P _,
  .

{foo} game:
  ~push [ *target 1, *type 'dahan ].

{turn} turn:
  ~spirit-phase,
  ~invader-phase,
  ~slow-phase,
  ~time-passes.

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

### Card Definitions

# Call to Isolation
{target-call} target-power: *power P,
  name P 'call-to-isolation,
  choose 1 (
    player-land .player Land,
    range Land 1 T,
    located .dahan T ),
  ~activate-power [ *target T ].


{activate-call} activate-power: *power P,
  name P 'call-to-isolation,
  branch (
    ( push-invaders:
      located .dahan .target,
      ~push [ *type 'explorer, *type 'town ])
    ( push-dahan: ~push [ *type 'dahan ] )
  ).

### Core Actions

move:
  *it I, *to T,
  +located I -> T.

push:
  choose 1 (
    located T -> .*target,
    *type X, ^X T,
    adjacent .*target L,
  ),
  ~move [*it T, *to L].

### Utilities
mk-card:
  +card C,
  +name C .*name,
  +located C -> .deck.

