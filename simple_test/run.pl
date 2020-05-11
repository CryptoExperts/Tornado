#!/usr/bin/perl

use strict;
use warnings;
use v5.14;

use FindBin;
chdir "$FindBin::Bin/..";

# Running tornado on a simple example
if (system("tornado -V -tp -ua-masked -o simple_test/ace_f.c simple_test/ace_f.ua")) {
    say "[error] tornado exited with a non-zero status code.";
    exit $?;
}

# Checking that the output contains a refresh
my $output = do {
    local $/ = undef;
    open my $FH, '<', 'simple_test/ace_f.c' or die $!;
    <$FH>;
};
if ($output !~ /REFRESH/) {
    say "[error] no refresh was inserted by tornado.";
    exit 1;
}

say "Tornado seems to work.";
