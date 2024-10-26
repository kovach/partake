game: () => (
  deck _, hand _,
  card 'summon_rat, card 'curse,
), !do (setup -> turn).

setup: deck D, card C, () => (located C D).
turn: deck D, hand H, 'rand chooses ~1 (located C D), (located C D) => (located C H).
turn: hand H, 'player chooses max 1 (located C H), !do [play | the-card C].

play: the-card 'summon_rat, () => (rat R).
play: the-card 'curse, RatCount := count (rat _).

turn -> !do turn.