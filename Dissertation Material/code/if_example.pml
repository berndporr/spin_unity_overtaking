if
:: (pos_autonomous == pos_oncoming) -> crashed = true;
:: (pos_autonomous == pos_other) -> crashed = true;
:: else -> skip;
fi
