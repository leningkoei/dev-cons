my $n = <STDIN>;
chomp($n);

my @array = ();
for (1..$n * 2) {
  my $input = <STDIN>;
  chomp($input);
  push(@array, $input);
}

my $result = 0;
sub swap {
  my ($array_ref, $i) = @_;
  my $j = $i + 1;
  ($array_ref->[$i], $array_ref->[$j]) = ($array_ref->[$j], $array_ref->[$i]);
  $result += 1;
}

sub find {
  my ($array_ref, $func_ref) = @_;
  my $length = scalar @$array_ref;

  for my $i (0..$length - 1) {
    my $result = $func_ref->($i, $array_ref->[$i]);
    if ($result) {
      return $i;
    } else {
    }
  }

  return -1;
}

sub swap_all {
  my ($array_ref, $begin, $end) = @_;
  for my $i (reverse $begin + 1 .. $end) {
    swap($array_ref, $i - 1);
  }
}

# print @array;
# print "\n";
# swap_all(\@array, 0, 3);
# print @array;
# print "\n";

my $begin = 0;
while ($begin != $n * 2) {
  my $target = $begin % $n + 1;
  if ($array[$begin] == $target) {
    $begin += 1;
  } else {
    my $f = sub {
      my ($i, $v) = @_;
      return ($i > $begin) && ($v == $target);
    };
    $target_index = find(\@array, $f);
    if ($target_index == -1) {
      $begin += 1;
    } else {
      swap_all(\@array, $begin, $target_index);
      $begin += 1;
    }
  }
}

print $result;
print "\n";
