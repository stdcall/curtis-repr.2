"""Bound quiet compilation and noisy sessions without skipping replies."""
from pathlib import Path
import queue
import sys
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'scripts'))
from check_lsp import receive_message  # noqa: E402


class LspDeadlineTests(unittest.TestCase):
    def test_quiet_compilation_can_finish_after_ninety_seconds(self):
        reply = {'method': 'tinymist/compileStatus',
                 'params': {'status': 'compileSuccess'}}
        inbox = Mock()
        inbox.get.side_effect = [queue.Empty, reply]
        process = Mock()
        process.poll.return_value = None
        with patch('check_lsp.time.monotonic', side_effect=[0, 120]):
            self.assertEqual(receive_message(inbox, process, 900), reply)
        self.assertEqual(inbox.get.call_count, 2)

    def test_expired_session_does_not_read_another_message(self):
        inbox = Mock()
        process = Mock()
        with patch('check_lsp.time.monotonic', return_value=10):
            with self.assertRaises(TimeoutError):
                receive_message(inbox, process, 10)
        inbox.get.assert_not_called()

    def test_server_exit_fails_without_waiting_for_the_whole_budget(self):
        inbox = Mock()
        inbox.get.side_effect = queue.Empty
        process = Mock()
        process.poll.return_value = 7
        with patch('check_lsp.time.monotonic', return_value=0):
            with self.assertRaisesRegex(RuntimeError, 'status 7'):
                receive_message(inbox, process, 900)
        self.assertEqual(inbox.get.call_count, 1)

    def test_notifications_cannot_extend_the_shared_deadline(self):
        inbox = queue.Queue()
        notices = [{'method': 'progress', 'params': n} for n in range(3)]
        for notice in notices:
            inbox.put(notice)
        process = Mock()
        with patch('check_lsp.time.monotonic', side_effect=[0, 899, 901]):
            self.assertEqual(receive_message(inbox, process, 900), notices[0])
            self.assertEqual(receive_message(inbox, process, 900), notices[1])
            with self.assertRaises(TimeoutError):
                receive_message(inbox, process, 900)
        self.assertEqual(inbox.qsize(), 1)


if __name__ == '__main__':
    unittest.main()
