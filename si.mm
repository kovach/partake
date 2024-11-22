game: +(player p1, player p2,
  play-area _,
  deck D,
  card X1, located X1 D,
  card X2, located X2 D,
  card X3, located X3 D,
), !do (setup-players -> turn).

setup-players: player P, +(hand P x, choose-area P y).

move: it T, to D, -(located T _), +(located T D).

turn: !do (grow-stage -> play-stage).
  grow-stage: player P, !do [(grow -> play) | the-player P].
    grow: !do (deal-cards -> choose-card).
      deal-cards: the-player P, deck D, choose-area P A,
        'rand chooses ~2 (located C D),
        !do [move | it C, to A].

      choose-card: the-player P, hand P H, choose-area P A,
        'player chooses 1 (located C A),
        !do [move | it C, to H].
        # then: move remaining cards to discard
    play: the-player P, hand P H, play-area In-play,
      P chooses ~1 (located C H),
      !do [move | it C, to In-play].

  play-stage: play-area A, located C A, !do [activate | the-card C].

    #play:
    #  .player chooses 1 (located C .player.hand),
    #  !do [move | it C, to .play-area].
