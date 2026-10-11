"""Archive round-trip, integrity and overwrite protection checks (no Lean/network)."""
import gzip
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import workspace_data as data


class WorkspaceDataTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        self.payload = b'original evidence\r\n' * 100
        self.entry = {'path': 'missions/sample/verification/result.json',
                      'bytes': len(self.payload), 'sha256': hashlib.sha256(self.payload).hexdigest()}
        self.object = data.object_path(self.root, self.entry['sha256'])
        self.object.parent.mkdir(parents=True)
        self.object.write_bytes(gzip.compress(self.payload, mtime=0))

    def test_round_trip_and_repeat_preserve_exact_bytes(self):
        data.restore(self.root, [self.entry])
        target = self.root / self.entry['path']
        self.assertEqual(target.read_bytes(), self.payload)
        data.restore(self.root, [self.entry])
        self.assertEqual(target.read_bytes(), self.payload)

    def test_changed_local_file_is_preserved(self):
        target = self.root / self.entry['path']
        target.parent.mkdir(parents=True)
        target.write_bytes(b'new local research')
        with self.assertRaisesRegex(ValueError, 'overwrite'):
            data.restore(self.root, [self.entry])
        self.assertEqual(target.read_bytes(), b'new local research')

    def test_corrupt_object_does_not_create_destination(self):
        self.object.write_bytes(gzip.compress(b'different data', mtime=0))
        with self.assertRaisesRegex(ValueError, 'mismatch'):
            data.restore(self.root, [self.entry])
        self.assertFalse((self.root / self.entry['path']).exists())

    def test_paths_cannot_escape_workspace(self):
        for path in ['../outside', '/absolute', 'D:/outside', 'missions/../../outside', 'missions\\bad']:
            with self.assertRaises(ValueError):
                data.inside(self.root, path)

    def test_pack_keeps_original_and_preserves_existing_ignore_rules(self):
        target = self.root / self.entry['path']
        target.parent.mkdir(parents=True)
        target.write_bytes(self.payload)
        (self.root / 'missions/index.json').write_text(json.dumps({'missions': [{'slug': 'sample'}]}))
        ignore = self.root / 'missions/sample/.gitignore'
        ignore.write_text('/runtime/\n')
        with patch.object(data.subprocess, 'check_output', return_value=(self.entry['path'] + '\0').encode()):
            data.pack(self.root, ['sample'], 1)
        self.assertEqual(target.read_bytes(), self.payload)
        self.assertEqual(data.read_index(self.root), [self.entry])
        self.assertIn('/runtime/\n', ignore.read_text())
        data.update_ignores(self.root, [self.entry])
        self.assertEqual(ignore.read_text().count(data.BEGIN), 1)

    def test_oversized_payload_is_rejected(self):
        entry = dict(self.entry, bytes=1)
        with self.assertRaisesRegex(ValueError, 'size mismatch'):
            data.restore(self.root, [entry])


if __name__ == '__main__':
    unittest.main()
