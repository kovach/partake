game: () ! (
  card_in_deck 'summon_rat,
  card_in_deck 'curse
), do turn.

turn: 'rand chooses 1 (card_in_deck C), (card_in_deck C) ! (card_in_hand C), done.
turn: 'player chooses 1 (card_in_hand C), do [play | the-card C], done.

play: the-card 'summon_rat, ()! (rat R), done.
play: the-card 'curse, RatCount := count (rat _), done.