{turn1} game: ~turn [ *count 1].
{setup} game:
  +player 'P,
  +dahan D,
  +located D -> 1,
  +play-area _,

  player P,
  +hand P H,
  +card-plays P -> 2,
  .

{deal} game:
  +deck D,
  ~mk-card [ *name 'instruments ],
  ~mk-card [ *name 'call ],
  player P,
  +choose-area P _,
  .

{foo} game:
  ~push [ *target 1, *type 'dahan ],
  branch ( (a: ~a) (b: ~b) ),
  player P,
  +energy P -> 2,
  .

{turn} turn:
  ~spirit-phase,
  ~power-phase,
  ~invader-phase,
  ~time-passes.

power-phase:
  choose 1 (located Card -> .play-area),
  ~target-power [ *power Card ],
  .

spirit-phase:
  player P,
  ~spirit-grow [ *player P ],
  ~play-cards [ *player P ].

spirit-grow:
  ~deal-cards [ *player .*player ].

deal-cards: *player P,
  ( choose (random 4) (
    located C -> .deck
    ), ~move [ *it C, *to P.choose-area ] ),
  ~choose-card [ *player P ].

  choose-card: *player P,
    choose 1 (
      located C -> P.choose-area,
      card-name C Name),
    ~move [ *it C, *to P.hand ].

play-cards: *player P,
  card-plays P -> CP,
  @lt 0 CP,
  energy P -> E,
  choose 1 (
    located Card -> P.hand,
    card-cost Card Cost,
    @le Cost E
  ),
  +energy P -> (- Cost),
  +card-plays P -> (-1),
  ~move [ *it Card, *to .play-area ],
  ~play-cards.

### Card Definitions

# Call to Isolation
{target-call} target-power: *power P,
  card-name P 'call-to-isolation,
  choose 1 (
    player-land .player Land,
    range Land 1 T,
    located .dahan T ),
  ~activate-power [ *target T ].


{activate-call} activate-power: *power P,
  card-name P 'call-to-isolation,
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
    range .*target L -> 1,
  ),
  ~move [*it T, *to L].

### Utilities
mk-card: *name N,
  +card C,
  +card-name C N,
  +located C -> .deck.

mk-card:
  card-name C 'call,
  +card-cost C 0.

mk-card:
  card-name C 'instruments,
  +card-cost C 4.
