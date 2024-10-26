game: () ! (
  deck _, hand _,
  card 'summon_rat, card 'curse,
), do (setup -> turn).

setup: deck D, card C, () ! (located C D), done.
turn: deck D, hand H, 'rand chooses ~1 (located C D), (located C D) ! (located C H), done.
turn: hand H, 'player chooses max 1 (located C H), do [play | the-card C], done.

play: the-card 'summon_rat, ()! (rat R), done.
play: the-card 'curse, RatCount := count (rat _), done.

turn -> do turn.