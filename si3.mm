{turn1} game: ~turn.

{setup} game:
  player P,
  ~place-presence [ *player P],
  .

{deal} game:
  +deck D,
  ~mk-card [ *name 'instruments ],
  ~mk-card [ *name 'call ],
  ~mk-card [ *name 'guard-healing ],
  player P,
  +choose-area P _,
  .

{foo} game:
  ~push [ *from 1, *type 'dahan ],
  branch ( (a: ~a) (b: ~b) ),
  player P,
  ~player := P,
  ~foo := ~player,
  +energy P -> 2,
  if (player P),
  not (player P),
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
  ( choose 1 (
      located C -> P.choose-area,
      card-name C Name),
    +owner C -> P,
    ~move [ *it C, *to P.hand ] ),
  ( located C -> P.choose-area,
    ~move [ *it C, *to .discard-area ] ).

play-cards: *player P,
  card-plays P -> CP,
  @lt 0 CP,
  energy P -> E,
  choose 1 (
    located Card -> P.hand,
    @le Card.card-cost E
  ),
  +energy P -> (- Card.card-cost),
  +card-plays P -> (-1),
  ~move [ *it Card, *to .play-area ],
  ~play-cards.

### Card Definitions

# Call to Isolation
{target-call}
target-power: *power P,
  owner P -> Player,
  card-name P 'call,
  choose 1 (
    player-land Player Land,
    range Land T -> 1,
    located .dahan -> T,
  ),
  ~activate-power [ *power P, *target T ].


{activate-call} activate-power: *power P,
  card-name P 'call,
  branch (
    ( push-invaders:
      located .dahan .*target,
      ~push [ *from .*target,
              *type 'explorer, *type 'town ])
    ( push-dahan: ~push [ *from .*target, *type 'dahan ] )
  ).

# Guard the Healing Land
target-power: *power Pow,
  owner Pow -> P,
  card-name Pow 'guard-healing,
  choose 1 (
    sacred-site P Land,
    range Land T -> 1,
  ),
  ~activate-power [ *power Pow, *target T ].

activate-power: *power C,
  card-name C 'guard-healing,
  ~remove-blight [ *from .*target ],
  ~defend [ *target .*target, *amount 4 ].


### Core Actions

move:
  *it I, *to T,
  +located I -> T.

defend: +[turn] land-defense .*target -> .*amount.

# land-defense/1/+
invaders-deal-damage:
  land-defense .*target -> D,
  +[invaders-deal-damage]
    invader-damage .*target -> (-D).

place-presence: *player P,
  choose 1 (land L),
  +presence Token P,
  +located Token -> L.

push:
  choose 1 (
    located T -> .*from,
    *type X, ^X T,
    range .*from L -> 1,
  ),
  ~move [*it T, *to L].

### Utilities
mk-card: *name N,
  +card C,
  +card-name C N,
  +located C -> .deck.

#mk-card: *name C 'call, +card-cost C 1,
#  #range C -> 1,
#  # ???
#  #restriction { L | located .dahan -> L },
#  .
#mk-card: *name 'instruments, +card-cost C 4.
#mk-card: *name 'guard-healing, +card-cost C 3.


### Invader turn
invader-phase: ~ravage.
ravage:
  active-ravage-card _ Type,
  type L Type,
  ~do-ravage [ *location L ].

#do-ravage: *location L,

