game: +(player p1, player p2,
  play-area _,
  deck D,
  card X1, located X1 D,
  card X2, located X2 D,
  card X3, located X3 D,
), !do (setup-players -> turn).

setup-players: player P, +(hand P x, choose-area P y).

move: -(located .it _), +(located .it .to).

turn: !do (grow-stage -> play-stage).
  grow-stage: player P, !do [(grow -> play) | the-player P].
    grow: !do (deal-cards -> choose-card).
      # atomic
      deal-cards: 'rand chooses ~2 (located C .deck),
                  !do [move | it C, to .the-player.choose-area].

      choose-card: the-player P,
        'player chooses 1 (located C P.choose-area),
        !do [move | it C, to P.hand].
        # then: move remaining cards to discard

    play:
      'player chooses ~1 (located C .the-player.hand),
      !do [move | it C, to .play-area].

  play-stage: play-area A, located C A, !do [activate | the-card C].
